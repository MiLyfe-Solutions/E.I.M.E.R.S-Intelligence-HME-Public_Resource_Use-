import V185TrunkScan21Chunk084

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1031805 : List Nat := [1, 4, 1, 1, 4, 1, 4, 1, 4]
def baseStart_1031805 : Nat := 118140960795 + 1031805 * 2 ^ 59
def prefixEnd_1031805 : Nat := 4983230072969 + 3 ^ 40 * 1031805 * 2
def baseEnd_1031805 : Nat := 235471958538862574174365

theorem tailTrace_1031805 : CollatzResearch.WordTrace tailWord_1031805 prefixEnd_1031805 235471958538862574174365 := by
  unfold tailWord_1031805
  simp only [CollatzResearch.WordTrace]
  refine ⟨37633020026954178109656869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25088680017969452073104579 37633020026954178109656869)
  ·
    refine ⟨7056191255053908395560663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37633020026954178109656869 7056191255053908395560663)
    ·
      refine ⟨10584286882580862593340995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7056191255053908395560663 10584286882580862593340995)
      ·
        refine ⟨15876430323871293890011493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10584286882580862593340995 15876430323871293890011493)
        ·
          refine ⟨2976830685725867604377155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15876430323871293890011493 2976830685725867604377155)
          ·
            refine ⟨4465246028588801406565733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2976830685725867604377155 4465246028588801406565733)
            ·
              refine ⟨837233630360400263731075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4465246028588801406565733 837233630360400263731075)
              ·
                refine ⟨1255850445540600395596613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837233630360400263731075 1255850445540600395596613)
                ·
                  refine ⟨235471958538862574174365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1255850445540600395596613 235471958538862574174365)
                  ·
                    rfl

theorem cell21_1031805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_1031805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1031805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1031805 prefixEnd_1031805 := by exact prefixLift 1031805
  have htrace : WordTrace (prefixWord ++ tailWord_1031805) baseStart_1031805 baseEnd_1031805 := by
    simpa [prefixWord, tailWord_1031805, baseEnd_1031805] using wordTrace_append hprefix tailTrace_1031805
  have hstable : (prefixWord ++ tailWord_1031805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031805).length < 2 ^ (prefixWord ++ tailWord_1031805).sum := by decide
  have hdescent : baseEnd_1031805 < baseStart_1031805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031842 : List Nat := [3, 3, 1, 4, 2, 1, 2, 2, 3]
def baseStart_1031842 : Nat := 118140960795 + 1031842 * 2 ^ 59
def prefixEnd_1031842 : Nat := 4983230072969 + 3 ^ 40 * 1031842 * 2
def baseEnd_1031842 : Nat := 235480402442958732057623

theorem tailTrace_1031842 : CollatzResearch.WordTrace tailWord_1031842 prefixEnd_1031842 235480402442958732057623 := by
  unfold tailWord_1031842
  simp only [CollatzResearch.WordTrace]
  refine ⟨9408592381955033357188445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25089579685213422285835853 9408592381955033357188445)
  ·
    refine ⟨3528222143233137508945667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9408592381955033357188445 3528222143233137508945667)
    ·
      refine ⟨5292333214849706263418501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3528222143233137508945667 5292333214849706263418501)
      ·
        refine ⟨992312477784319924390969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5292333214849706263418501 992312477784319924390969)
        ·
          refine ⟨744234358338239943293227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 992312477784319924390969 744234358338239943293227)
          ·
            refine ⟨1116351537507359914939841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744234358338239943293227 1116351537507359914939841)
            ·
              refine ⟨837263653130519936204881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1116351537507359914939841 837263653130519936204881)
              ·
                refine ⟨627947739847889952153661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 837263653130519936204881 627947739847889952153661)
                ·
                  refine ⟨235480402442958732057623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627947739847889952153661 235480402442958732057623)
                  ·
                    rfl

theorem cell21_1031842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_1031842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1031842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1031842 prefixEnd_1031842 := by exact prefixLift 1031842
  have htrace : WordTrace (prefixWord ++ tailWord_1031842) baseStart_1031842 baseEnd_1031842 := by
    simpa [prefixWord, tailWord_1031842, baseEnd_1031842] using wordTrace_append hprefix tailTrace_1031842
  have hstable : (prefixWord ++ tailWord_1031842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031842).length < 2 ^ (prefixWord ++ tailWord_1031842).sum := by decide
  have hdescent : baseEnd_1031842 < baseStart_1031842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031909 : List Nat := [1, 3, 1, 4, 1, 1, 4, 1, 5]
def baseStart_1031909 : Nat := 118140960795 + 1031909 * 2 ^ 59
def prefixEnd_1031909 : Nat := 4983230072969 + 3 ^ 40 * 1031909 * 2
def baseEnd_1031909 : Nat := 235495692755781504440819

theorem tailTrace_1031909 : CollatzResearch.WordTrace tailWord_1031909 prefixEnd_1031909 235495692755781504440819 := by
  unfold tailWord_1031909
  simp only [CollatzResearch.WordTrace]
  refine ⟨37636813218577403871442781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25091208812384935914295187 37636813218577403871442781)
  ·
    refine ⟨14113804956966526451791043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37636813218577403871442781 14113804956966526451791043)
    ·
      refine ⟨21170707435449789677686565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14113804956966526451791043 21170707435449789677686565)
      ·
        refine ⟨3969507644146835564566231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21170707435449789677686565 3969507644146835564566231)
        ·
          refine ⟨5954261466220253346849347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3969507644146835564566231 5954261466220253346849347)
          ·
            refine ⟨8931392199330380020274021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5954261466220253346849347 8931392199330380020274021)
            ·
              refine ⟨1674636037374446253801379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8931392199330380020274021 1674636037374446253801379)
              ·
                refine ⟨2511954056061669380702069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674636037374446253801379 2511954056061669380702069)
                ·
                  refine ⟨235495692755781504440819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2511954056061669380702069 235495692755781504440819)
                  ·
                    rfl

theorem cell21_1031909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_1031909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1031909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1031909 prefixEnd_1031909 := by exact prefixLift 1031909
  have htrace : WordTrace (prefixWord ++ tailWord_1031909) baseStart_1031909 baseEnd_1031909 := by
    simpa [prefixWord, tailWord_1031909, baseEnd_1031909] using wordTrace_append hprefix tailTrace_1031909
  have hstable : (prefixWord ++ tailWord_1031909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031909).length < 2 ^ (prefixWord ++ tailWord_1031909).sum := by decide
  have hdescent : baseEnd_1031909 < baseStart_1031909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031923 : List Nat := [1, 1, 1, 2, 2, 3, 2, 5, 4]
def baseStart_1031923 : Nat := 118140960795 + 1031923 * 2 ^ 59
def prefixEnd_1031923 : Nat := 4983230072969 + 3 ^ 40 * 1031923 * 2
def baseEnd_1031923 : Nat := 235498887746520591207457

theorem tailTrace_1031923 : CollatzResearch.WordTrace tailWord_1031923 prefixEnd_1031923 235498887746520591207457 := by
  unfold tailWord_1031923
  simp only [CollatzResearch.WordTrace]
  refine ⟨37637323840526684262452423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25091549227017789508301615 37637323840526684262452423)
  ·
    refine ⟨56455985760790026393678635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37637323840526684262452423 56455985760790026393678635)
    ·
      refine ⟨84683978641185039590517953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56455985760790026393678635 84683978641185039590517953)
      ·
        refine ⟨63512983980888779692888465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84683978641185039590517953 63512983980888779692888465)
        ·
          refine ⟨47634737985666584769666349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63512983980888779692888465 47634737985666584769666349)
          ·
            refine ⟨17863026744624969288624881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47634737985666584769666349 17863026744624969288624881)
            ·
              refine ⟨13397270058468726966468661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17863026744624969288624881 13397270058468726966468661)
              ·
                refine ⟨1255994067981443153106437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13397270058468726966468661 1255994067981443153106437)
                ·
                  refine ⟨235498887746520591207457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1255994067981443153106437 235498887746520591207457)
                  ·
                    rfl

theorem cell21_1031923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 4].length) (baseStart_1031923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1031923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1031923 prefixEnd_1031923 := by exact prefixLift 1031923
  have htrace : WordTrace (prefixWord ++ tailWord_1031923) baseStart_1031923 baseEnd_1031923 := by
    simpa [prefixWord, tailWord_1031923, baseEnd_1031923] using wordTrace_append hprefix tailTrace_1031923
  have hstable : (prefixWord ++ tailWord_1031923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031923).length < 2 ^ (prefixWord ++ tailWord_1031923).sum := by decide
  have hdescent : baseEnd_1031923 < baseStart_1031923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032044 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 7]
def baseStart_1032044 : Nat := 118140960795 + 1032044 * 2 ^ 59
def prefixEnd_1032044 : Nat := 4983230072969 + 3 ^ 40 * 1032044 * 2
def baseEnd_1032044 : Nat := 235526501595051269690543

theorem tailTrace_1032044 : CollatzResearch.WordTrace tailWord_1032044 prefixEnd_1032044 235526501595051269690543 := by
  unfold tailWord_1032044
  simp only [CollatzResearch.WordTrace]
  refine ⟨18820868536544160963803593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25094491382058881285071457 18820868536544160963803593)
  ·
    refine ⟨14115651402408120722852695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18820868536544160963803593 14115651402408120722852695)
    ·
      refine ⟨21173477103612181084279043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14115651402408120722852695 21173477103612181084279043)
      ·
        refine ⟨31760215655418271626418565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21173477103612181084279043 31760215655418271626418565)
        ·
          refine ⟨5955040435390925929953481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31760215655418271626418565 5955040435390925929953481)
          ·
            refine ⟨4466280326543194447465111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5955040435390925929953481 4466280326543194447465111)
            ·
              refine ⟨6699420489814791671197667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4466280326543194447465111 6699420489814791671197667)
              ·
                refine ⟨10049130734722187506796501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6699420489814791671197667 10049130734722187506796501)
                ·
                  refine ⟨235526501595051269690543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10049130734722187506796501 235526501595051269690543)
                  ·
                    rfl

theorem cell21_1032044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_1032044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1032044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1032044 prefixEnd_1032044 := by exact prefixLift 1032044
  have htrace : WordTrace (prefixWord ++ tailWord_1032044) baseStart_1032044 baseEnd_1032044 := by
    simpa [prefixWord, tailWord_1032044, baseEnd_1032044] using wordTrace_append hprefix tailTrace_1032044
  have hstable : (prefixWord ++ tailWord_1032044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032044).length < 2 ^ (prefixWord ++ tailWord_1032044).sum := by decide
  have hdescent : baseEnd_1032044 < baseStart_1032044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032151 : List Nat := [1, 1, 3, 2, 1, 1, 5, 3, 4]
def baseStart_1032151 : Nat := 118140960795 + 1032151 * 2 ^ 59
def prefixEnd_1032151 : Nat := 4983230072969 + 3 ^ 40 * 1032151 * 2
def baseEnd_1032151 : Nat := 235550920452842861406991

theorem tailTrace_1032151 : CollatzResearch.WordTrace tailWord_1032151 prefixEnd_1032151 235550920452842861406991 := by
  unfold tailWord_1032151
  simp only [CollatzResearch.WordTrace]
  refine ⟨37645639683700679201752307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25097093122467119467834871 37645639683700679201752307)
  ·
    refine ⟨56468459525551018802628461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37645639683700679201752307 56468459525551018802628461)
    ·
      refine ⟨21175672322081632050985673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56468459525551018802628461 21175672322081632050985673)
      ·
        refine ⟨15881754241561224038239255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21175672322081632050985673 15881754241561224038239255)
        ·
          refine ⟨23822631362341836057358883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15881754241561224038239255 23822631362341836057358883)
          ·
            refine ⟨35733947043512754086038325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23822631362341836057358883 35733947043512754086038325)
            ·
              refine ⟨3350057535329320695566093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35733947043512754086038325 3350057535329320695566093)
              ·
                refine ⟨1256271575748495260837285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3350057535329320695566093 1256271575748495260837285)
                ·
                  refine ⟨235550920452842861406991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1256271575748495260837285 235550920452842861406991)
                  ·
                    rfl

theorem cell21_1032151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 4].length) (baseStart_1032151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1032151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1032151 prefixEnd_1032151 := by exact prefixLift 1032151
  have htrace : WordTrace (prefixWord ++ tailWord_1032151) baseStart_1032151 baseEnd_1032151 := by
    simpa [prefixWord, tailWord_1032151, baseEnd_1032151] using wordTrace_append hprefix tailTrace_1032151
  have hstable : (prefixWord ++ tailWord_1032151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032151).length < 2 ^ (prefixWord ++ tailWord_1032151).sum := by decide
  have hdescent : baseEnd_1032151 < baseStart_1032151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032182 : List Nat := [5, 1, 1, 1, 4, 9]
def baseStart_1032182 : Nat := 118140960795 + 1032182 * 2 ^ 59
def prefixEnd_1032182 : Nat := 4983230072969 + 3 ^ 40 * 1032182 * 2
def baseEnd_1032182 : Nat := 8724370187970136903343

theorem tailTrace_1032182 : CollatzResearch.WordTrace tailWord_1032182 prefixEnd_1032182 8724370187970136903343 := by
  unfold tailWord_1032182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2352923146661773218508175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25097846897725580997420533 2352923146661773218508175)
  ·
    refine ⟨3529384719992659827762263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2352923146661773218508175 3529384719992659827762263)
    ·
      refine ⟨5294077079988989741643395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3529384719992659827762263 5294077079988989741643395)
      ·
        refine ⟨7941115619983484612465093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5294077079988989741643395 7941115619983484612465093)
        ·
          refine ⟨1488959178746903364837205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7941115619983484612465093 1488959178746903364837205)
          ·
            refine ⟨8724370187970136903343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1488959178746903364837205 8724370187970136903343)
            ·
              rfl

theorem cell21_1032182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 9].length) (baseStart_1032182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1032182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1032182 prefixEnd_1032182 := by exact prefixLift 1032182
  have htrace : WordTrace (prefixWord ++ tailWord_1032182) baseStart_1032182 baseEnd_1032182 := by
    simpa [prefixWord, tailWord_1032182, baseEnd_1032182] using wordTrace_append hprefix tailTrace_1032182
  have hstable : (prefixWord ++ tailWord_1032182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032182).length < 2 ^ (prefixWord ++ tailWord_1032182).sum := by decide
  have hdescent : baseEnd_1032182 < baseStart_1032182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032213 : List Nat := [1, 3, 2, 1, 5, 1, 1, 2, 5]
def baseStart_1032213 : Nat := 118140960795 + 1032213 * 2 ^ 59
def prefixEnd_1032213 : Nat := 4983230072969 + 3 ^ 40 * 1032213 * 2
def baseEnd_1032213 : Nat := 235565069697544531373531

theorem tailTrace_1032213 : CollatzResearch.WordTrace tailWord_1032213 prefixEnd_1032213 235565069697544531373531 := by
  unfold tailWord_1032213
  simp only [CollatzResearch.WordTrace]
  refine ⟨37647901009476063790509293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25098600672984042527006195 37647901009476063790509293)
  ·
    refine ⟨14117962878553523921440985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37647901009476063790509293 14117962878553523921440985)
    ·
      refine ⟨10588472158915142941080739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14117962878553523921440985 10588472158915142941080739)
      ·
        refine ⟨15882708238372714411621109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10588472158915142941080739 15882708238372714411621109)
        ·
          refine ⟨1489003897347441976089479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15882708238372714411621109 1489003897347441976089479)
          ·
            refine ⟨2233505846021162964134219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1489003897347441976089479 2233505846021162964134219)
            ·
              refine ⟨3350258769031744446201329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2233505846021162964134219 3350258769031744446201329)
              ·
                refine ⟨2512694076773808334650997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3350258769031744446201329 2512694076773808334650997)
                ·
                  refine ⟨235565069697544531373531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2512694076773808334650997 235565069697544531373531)
                  ·
                    rfl

theorem cell21_1032213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_1032213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1032213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1032213 prefixEnd_1032213 := by exact prefixLift 1032213
  have htrace : WordTrace (prefixWord ++ tailWord_1032213) baseStart_1032213 baseEnd_1032213 := by
    simpa [prefixWord, tailWord_1032213, baseEnd_1032213] using wordTrace_append hprefix tailTrace_1032213
  have hstable : (prefixWord ++ tailWord_1032213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032213).length < 2 ^ (prefixWord ++ tailWord_1032213).sum := by decide
  have hdescent : baseEnd_1032213 < baseStart_1032213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032241 : List Nat := [1, 2, 2, 3, 1, 4, 8]
def baseStart_1032241 : Nat := 118140960795 + 1032241 * 2 ^ 59
def prefixEnd_1032241 : Nat := 4983230072969 + 3 ^ 40 * 1032241 * 2
def baseEnd_1032241 : Nat := 26174606631002522767423

theorem tailTrace_1032241 : CollatzResearch.WordTrace tailWord_1032241 prefixEnd_1032241 26174606631002522767423 := by
  unfold tailWord_1032241
  simp only [CollatzResearch.WordTrace]
  refine ⟨37648922253374624572528577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25099281502249749715019051 37648922253374624572528577)
  ·
    refine ⟨28236691690030968429396433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37648922253374624572528577 28236691690030968429396433)
    ·
      refine ⟨21177518767523226322047325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28236691690030968429396433 21177518767523226322047325)
      ·
        refine ⟨7941569537821209870767747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21177518767523226322047325 7941569537821209870767747)
        ·
          refine ⟨11912354306731814806151621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7941569537821209870767747 11912354306731814806151621)
          ·
            refine ⟨2233566432512215276153429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11912354306731814806151621 2233566432512215276153429)
            ·
              refine ⟨26174606631002522767423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2233566432512215276153429 26174606631002522767423)
              ·
                rfl

theorem cell21_1032241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 8].length) (baseStart_1032241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1032241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1032241 prefixEnd_1032241 := by exact prefixLift 1032241
  have htrace : WordTrace (prefixWord ++ tailWord_1032241) baseStart_1032241 baseEnd_1032241 := by
    simpa [prefixWord, tailWord_1032241, baseEnd_1032241] using wordTrace_append hprefix tailTrace_1032241
  have hstable : (prefixWord ++ tailWord_1032241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032241).length < 2 ^ (prefixWord ++ tailWord_1032241).sum := by decide
  have hdescent : baseEnd_1032241 < baseStart_1032241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032317 : List Nat := [1, 4, 1, 1, 3, 2, 1, 8]
def baseStart_1032317 : Nat := 118140960795 + 1032317 * 2 ^ 59
def prefixEnd_1032317 : Nat := 4983230072969 + 3 ^ 40 * 1032317 * 2
def baseEnd_1032317 : Nat := 78529601304821153879995

theorem tailTrace_1032317 : CollatzResearch.WordTrace tailWord_1032317 prefixEnd_1032317 78529601304821153879995 := by
  unfold tailWord_1032317
  simp only [CollatzResearch.WordTrace]
  refine ⟨37651694201099289552295205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25101129467399526368196803 37651694201099289552295205)
  ·
    refine ⟨7059692662706116791055351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37651694201099289552295205 7059692662706116791055351)
    ·
      refine ⟨10589538994059175186583027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7059692662706116791055351 10589538994059175186583027)
      ·
        refine ⟨15884308491088762779874541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10589538994059175186583027 15884308491088762779874541)
        ·
          refine ⟨5956615684158286042452953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15884308491088762779874541 5956615684158286042452953)
          ·
            refine ⟨4467461763118714531839715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5956615684158286042452953 4467461763118714531839715)
            ·
              refine ⟨6701192644678071797759573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4467461763118714531839715 6701192644678071797759573)
              ·
                refine ⟨78529601304821153879995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6701192644678071797759573 78529601304821153879995)
                ·
                  rfl

theorem cell21_1032317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 8].length) (baseStart_1032317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1032317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1032317 prefixEnd_1032317 := by exact prefixLift 1032317
  have htrace : WordTrace (prefixWord ++ tailWord_1032317) baseStart_1032317 baseEnd_1032317 := by
    simpa [prefixWord, tailWord_1032317, baseEnd_1032317] using wordTrace_append hprefix tailTrace_1032317
  have hstable : (prefixWord ++ tailWord_1032317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032317).length < 2 ^ (prefixWord ++ tailWord_1032317).sum := by decide
  have hdescent : baseEnd_1032317 < baseStart_1032317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032407 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 9]
def baseStart_1032407 : Nat := 118140960795 + 1032407 * 2 ^ 59
def prefixEnd_1032407 : Nat := 4983230072969 + 3 ^ 40 * 1032407 * 2
def baseEnd_1032407 : Nat := 235609343140643305139801

theorem tailTrace_1032407 : CollatzResearch.WordTrace tailWord_1032407 prefixEnd_1032407 235609343140643305139801 := by
  unfold tailWord_1032407
  simp only [CollatzResearch.WordTrace]
  refine ⟨37654976770773234923071475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25103317847182156615380983 37654976770773234923071475)
  ·
    refine ⟨56482465156159852384607213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37654976770773234923071475 56482465156159852384607213)
    ·
      refine ⟨21180924433559944644227705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56482465156159852384607213 21180924433559944644227705)
      ·
        refine ⟨15885693325169958483170779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21180924433559944644227705 15885693325169958483170779)
        ·
          refine ⟨23828539987754937724756169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15885693325169958483170779 23828539987754937724756169)
          ·
            refine ⟨17871404990816203293567127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23828539987754937724756169 17871404990816203293567127)
            ·
              refine ⟨26807107486224304940350691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17871404990816203293567127 26807107486224304940350691)
              ·
                refine ⟨40210661229336457410526037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26807107486224304940350691 40210661229336457410526037)
                ·
                  refine ⟨235609343140643305139801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40210661229336457410526037 235609343140643305139801)
                  ·
                    rfl

theorem cell21_1032407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 9].length) (baseStart_1032407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1032407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1032407 prefixEnd_1032407 := by exact prefixLift 1032407
  have htrace : WordTrace (prefixWord ++ tailWord_1032407) baseStart_1032407 baseEnd_1032407 := by
    simpa [prefixWord, tailWord_1032407, baseEnd_1032407] using wordTrace_append hprefix tailTrace_1032407
  have hstable : (prefixWord ++ tailWord_1032407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032407).length < 2 ^ (prefixWord ++ tailWord_1032407).sum := by decide
  have hdescent : baseEnd_1032407 < baseStart_1032407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032413 : List Nat := [1, 4, 3, 2, 1, 3, 1, 2, 4]
def baseStart_1032413 : Nat := 118140960795 + 1032413 * 2 ^ 59
def prefixEnd_1032413 : Nat := 4983230072969 + 3 ^ 40 * 1032413 * 2
def baseEnd_1032413 : Nat := 235610712422388628039789

theorem tailTrace_1032413 : CollatzResearch.WordTrace tailWord_1032413 prefixEnd_1032413 235610712422388628039789 := by
  unfold tailWord_1032413
  simp only [CollatzResearch.WordTrace]
  refine ⟨37655195608751497947789893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25103463739167665298526595 37655195608751497947789893)
  ·
    refine ⟨7060349176640905865210605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37655195608751497947789893 7060349176640905865210605)
    ·
      refine ⟨2647630941240339699453977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7060349176640905865210605 2647630941240339699453977)
      ·
        refine ⟨1985723205930254774590483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2647630941240339699453977 1985723205930254774590483)
        ·
          refine ⟨2978584808895382161885725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1985723205930254774590483 2978584808895382161885725)
          ·
            refine ⟨1116969303335768310707147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2978584808895382161885725 1116969303335768310707147)
            ·
              refine ⟨1675453955003652466060721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1116969303335768310707147 1675453955003652466060721)
              ·
                refine ⟨1256590466252739349545541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1675453955003652466060721 1256590466252739349545541)
                ·
                  refine ⟨235610712422388628039789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1256590466252739349545541 235610712422388628039789)
                  ·
                    rfl

theorem cell21_1032413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_1032413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1032413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1032413 prefixEnd_1032413 := by exact prefixLift 1032413
  have htrace : WordTrace (prefixWord ++ tailWord_1032413) baseStart_1032413 baseEnd_1032413 := by
    simpa [prefixWord, tailWord_1032413, baseEnd_1032413] using wordTrace_append hprefix tailTrace_1032413
  have hstable : (prefixWord ++ tailWord_1032413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032413).length < 2 ^ (prefixWord ++ tailWord_1032413).sum := by decide
  have hdescent : baseEnd_1032413 < baseStart_1032413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032424 : List Nat := [2, 1, 4, 1, 2, 2, 1, 3, 5]
def baseStart_1032424 : Nat := 118140960795 + 1032424 * 2 ^ 59
def prefixEnd_1032424 : Nat := 4983230072969 + 3 ^ 40 * 1032424 * 2
def baseEnd_1032424 : Nat := 235613222772255053356433

theorem tailTrace_1032424 : CollatzResearch.WordTrace tailWord_1032424 prefixEnd_1032424 235613222772255053356433 := by
  unfold tailWord_1032424
  simp only [CollatzResearch.WordTrace]
  refine ⟨18827798405855823413220163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25103731207807764550960217 18827798405855823413220163)
  ·
    refine ⟨28241697608783735119830245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18827798405855823413220163 28241697608783735119830245)
    ·
      refine ⟨5295318301646950334968171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28241697608783735119830245 5295318301646950334968171)
      ·
        refine ⟨7942977452470425502452257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5295318301646950334968171 7942977452470425502452257)
        ·
          refine ⟨5957233089352819126839193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7942977452470425502452257 5957233089352819126839193)
          ·
            refine ⟨4467924817014614345129395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5957233089352819126839193 4467924817014614345129395)
            ·
              refine ⟨6701887225521921517694093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4467924817014614345129395 6701887225521921517694093)
              ·
                refine ⟨2513207709570720569135285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6701887225521921517694093 2513207709570720569135285)
                ·
                  refine ⟨235613222772255053356433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2513207709570720569135285 235613222772255053356433)
                  ·
                    rfl

theorem cell21_1032424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_1032424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1032424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1032424 prefixEnd_1032424 := by exact prefixLift 1032424
  have htrace : WordTrace (prefixWord ++ tailWord_1032424) baseStart_1032424 baseEnd_1032424 := by
    simpa [prefixWord, tailWord_1032424, baseEnd_1032424] using wordTrace_append hprefix tailTrace_1032424
  have hstable : (prefixWord ++ tailWord_1032424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032424).length < 2 ^ (prefixWord ++ tailWord_1032424).sum := by decide
  have hdescent : baseEnd_1032424 < baseStart_1032424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032528 : List Nat := [2, 1, 1, 1, 1, 15]
def baseStart_1032528 : Nat := 118140960795 + 1032528 * 2 ^ 59
def prefixEnd_1032528 : Nat := 4983230072969 + 3 ^ 40 * 1032528 * 2
def baseEnd_1032528 : Nat := 8727294703302740134181

theorem tailTrace_1032528 : CollatzResearch.WordTrace tailWord_1032528 prefixEnd_1032528 8727294703302740134181 := by
  unfold tailWord_1032528
  simp only [CollatzResearch.WordTrace]
  refine ⟨18829695001667436294113119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25106260002223248392150825 18829695001667436294113119)
  ·
    refine ⟨28244542502501154441169679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18829695001667436294113119 28244542502501154441169679)
    ·
      refine ⟨42366813753751731661754519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28244542502501154441169679 42366813753751731661754519)
      ·
        refine ⟨63550220630627597492631779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42366813753751731661754519 63550220630627597492631779)
        ·
          refine ⟨95325330945941396238947669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63550220630627597492631779 95325330945941396238947669)
          ·
            refine ⟨8727294703302740134181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 95325330945941396238947669 8727294703302740134181)
            ·
              rfl

theorem cell21_1032528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 15].length) (baseStart_1032528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1032528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1032528 prefixEnd_1032528 := by exact prefixLift 1032528
  have htrace : WordTrace (prefixWord ++ tailWord_1032528) baseStart_1032528 baseEnd_1032528 := by
    simpa [prefixWord, tailWord_1032528, baseEnd_1032528] using wordTrace_append hprefix tailTrace_1032528
  have hstable : (prefixWord ++ tailWord_1032528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032528).length < 2 ^ (prefixWord ++ tailWord_1032528).sum := by decide
  have hdescent : baseEnd_1032528 < baseStart_1032528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032562 : List Nat := [3, 2, 1, 2, 1, 4, 3, 5]
def baseStart_1032562 : Nat := 118140960795 + 1032562 * 2 ^ 59
def prefixEnd_1032562 : Nat := 4983230072969 + 3 ^ 40 * 1032562 * 2
def baseEnd_1032562 : Nat := 78548238750799160018717

theorem tailTrace_1032562 : CollatzResearch.WordTrace tailWord_1032562 prefixEnd_1032562 78548238750799160018717 := by
  unfold tailWord_1032562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9415157521302924098740985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25107086723474464263309293 9415157521302924098740985)
  ·
    refine ⟨7061368140977193074055739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9415157521302924098740985 7061368140977193074055739)
    ·
      refine ⟨10592052211465789611083609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7061368140977193074055739 10592052211465789611083609)
      ·
        refine ⟨7944039158599342208312707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10592052211465789611083609 7944039158599342208312707)
        ·
          refine ⟨11916058737899013312469061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7944039158599342208312707 11916058737899013312469061)
          ·
            refine ⟨2234261013356064996087949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11916058737899013312469061 2234261013356064996087949)
            ·
              refine ⟨837847880008524373532981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2234261013356064996087949 837847880008524373532981)
              ·
                refine ⟨78548238750799160018717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 837847880008524373532981 78548238750799160018717)
                ·
                  rfl

theorem cell21_1032562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_1032562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1032562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1032562 prefixEnd_1032562 := by exact prefixLift 1032562
  have htrace : WordTrace (prefixWord ++ tailWord_1032562) baseStart_1032562 baseEnd_1032562 := by
    simpa [prefixWord, tailWord_1032562, baseEnd_1032562] using wordTrace_append hprefix tailTrace_1032562
  have hstable : (prefixWord ++ tailWord_1032562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032562).length < 2 ^ (prefixWord ++ tailWord_1032562).sum := by decide
  have hdescent : baseEnd_1032562 < baseStart_1032562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032658 : List Nat := [3, 2, 2, 4, 1, 2, 2, 1, 4]
def baseStart_1032658 : Nat := 118140960795 + 1032658 * 2 ^ 59
def prefixEnd_1032658 : Nat := 4983230072969 + 3 ^ 40 * 1032658 * 2
def baseEnd_1032658 : Nat := 235666624760322646455955

theorem tailTrace_1032658 : CollatzResearch.WordTrace tailWord_1032658 prefixEnd_1032658 235666624760322646455955 := by
  unfold tailWord_1032658
  simp only [CollatzResearch.WordTrace]
  refine ⟨9416032873215976197614657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25109420995242603193639085 9416032873215976197614657)
  ·
    refine ⟨7062024654911982148210993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9416032873215976197614657 7062024654911982148210993)
    ·
      refine ⟨5296518491183986611158245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7062024654911982148210993 5296518491183986611158245)
      ·
        refine ⟨993097217096997489592171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5296518491183986611158245 993097217096997489592171)
        ·
          refine ⟨1489645825645496234388257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 993097217096997489592171 1489645825645496234388257)
          ·
            refine ⟨1117234369234122175791193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1489645825645496234388257 1117234369234122175791193)
            ·
              refine ⟨837925776925591631843395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1117234369234122175791193 837925776925591631843395)
              ·
                refine ⟨1256888665388387447765093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837925776925591631843395 1256888665388387447765093)
                ·
                  refine ⟨235666624760322646455955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1256888665388387447765093 235666624760322646455955)
                  ·
                    rfl

theorem cell21_1032658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_1032658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1032658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1032658 prefixEnd_1032658 := by exact prefixLift 1032658
  have htrace : WordTrace (prefixWord ++ tailWord_1032658) baseStart_1032658 baseEnd_1032658 := by
    simpa [prefixWord, tailWord_1032658, baseEnd_1032658] using wordTrace_append hprefix tailTrace_1032658
  have hstable : (prefixWord ++ tailWord_1032658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032658).length < 2 ^ (prefixWord ++ tailWord_1032658).sum := by decide
  have hdescent : baseEnd_1032658 < baseStart_1032658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032717 : List Nat := [1, 7, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1032717 : Nat := 118140960795 + 1032717 * 2 ^ 59
def prefixEnd_1032717 : Nat := 4983230072969 + 3 ^ 40 * 1032717 * 2
def baseEnd_1032717 : Nat := 235680089364151654972501

theorem tailTrace_1032717 : CollatzResearch.WordTrace tailWord_1032717 prefixEnd_1032717 235680089364151654972501 := by
  unfold tailWord_1032717
  simp only [CollatzResearch.WordTrace]
  refine ⟨37666283399650157866856405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25110855599766771911237603 37666283399650157866856405)
  ·
    refine ⟨882803517179300575004447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 37666283399650157866856405 882803517179300575004447)
    ·
      refine ⟨1324205275768950862506671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 882803517179300575004447 1324205275768950862506671)
      ·
        refine ⟨1986307913653426293760007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1324205275768950862506671 1986307913653426293760007)
        ·
          refine ⟨2979461870480139440640011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1986307913653426293760007 2979461870480139440640011)
          ·
            refine ⟨4469192805720209160960017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2979461870480139440640011 4469192805720209160960017)
            ·
              refine ⟨3351894604290156870720013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4469192805720209160960017 3351894604290156870720013)
              ·
                refine ⟨1256960476608808826520005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3351894604290156870720013 1256960476608808826520005)
                ·
                  refine ⟨235680089364151654972501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1256960476608808826520005 235680089364151654972501)
                  ·
                    rfl

theorem cell21_1032717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1032717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1032717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1032717 prefixEnd_1032717 := by exact prefixLift 1032717
  have htrace : WordTrace (prefixWord ++ tailWord_1032717) baseStart_1032717 baseEnd_1032717 := by
    simpa [prefixWord, tailWord_1032717, baseEnd_1032717] using wordTrace_append hprefix tailTrace_1032717
  have hstable : (prefixWord ++ tailWord_1032717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032717).length < 2 ^ (prefixWord ++ tailWord_1032717).sum := by decide
  have hdescent : baseEnd_1032717 < baseStart_1032717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032728 : List Nat := [2, 1, 2, 3, 3, 2, 1, 2, 5]
def baseStart_1032728 : Nat := 118140960795 + 1032728 * 2 ^ 59
def prefixEnd_1032728 : Nat := 4983230072969 + 3 ^ 40 * 1032728 * 2
def baseEnd_1032728 : Nat := 235682599714018080289145

theorem tailTrace_1032728 : CollatzResearch.WordTrace tailWord_1032728 prefixEnd_1032728 235682599714018080289145 := by
  unfold tailWord_1032728
  simp only [CollatzResearch.WordTrace]
  refine ⟨18833342301305153372753419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25111123068406871163671225 18833342301305153372753419)
  ·
    refine ⟨28250013451957730059130129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18833342301305153372753419 28250013451957730059130129)
    ·
      refine ⟨21187510088968297544347597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28250013451957730059130129 21187510088968297544347597)
      ·
        refine ⟨7945316283363111579130349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21187510088968297544347597 7945316283363111579130349)
        ·
          refine ⟨2979493606261166842173881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7945316283363111579130349 2979493606261166842173881)
          ·
            refine ⟨2234620204695875131630411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2979493606261166842173881 2234620204695875131630411)
            ·
              refine ⟨3351930307043812697445617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2234620204695875131630411 3351930307043812697445617)
              ·
                refine ⟨2513947730282859523084213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3351930307043812697445617 2513947730282859523084213)
                ·
                  refine ⟨235682599714018080289145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2513947730282859523084213 235682599714018080289145)
                  ·
                    rfl

theorem cell21_1032728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_1032728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1032728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1032728 prefixEnd_1032728 := by exact prefixLift 1032728
  have htrace : WordTrace (prefixWord ++ tailWord_1032728) baseStart_1032728 baseEnd_1032728 := by
    simpa [prefixWord, tailWord_1032728, baseEnd_1032728] using wordTrace_append hprefix tailTrace_1032728
  have hstable : (prefixWord ++ tailWord_1032728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032728).length < 2 ^ (prefixWord ++ tailWord_1032728).sum := by decide
  have hdescent : baseEnd_1032728 < baseStart_1032728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032832 : List Nat := [2, 1, 1, 2, 1, 5, 1, 8]
def baseStart_1032832 : Nat := 118140960795 + 1032832 * 2 ^ 59
def prefixEnd_1032832 : Nat := 4983230072969 + 3 ^ 40 * 1032832 * 2
def baseEnd_1032832 : Nat := 78568777976979003518533

theorem tailTrace_1032832 : CollatzResearch.WordTrace tailWord_1032832 prefixEnd_1032832 78568777976979003518533 := by
  unfold tailWord_1032832
  simp only [CollatzResearch.WordTrace]
  refine ⟨18835238897116766253646375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25113651862822355004861833 18835238897116766253646375)
  ·
    refine ⟨28252858345675149380469563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18835238897116766253646375 28252858345675149380469563)
    ·
      refine ⟨42379287518512724070704345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28252858345675149380469563 42379287518512724070704345)
      ·
        refine ⟨31784465638884543053028259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42379287518512724070704345 31784465638884543053028259)
        ·
          refine ⟨47676698458326814579542389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31784465638884543053028259 47676698458326814579542389)
          ·
            refine ⟨4469690480468138866832099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47676698458326814579542389 4469690480468138866832099)
            ·
              refine ⟨6704535720702208300248149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4469690480468138866832099 6704535720702208300248149)
              ·
                refine ⟨78568777976979003518533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6704535720702208300248149 78568777976979003518533)
                ·
                  rfl

theorem cell21_1032832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 8].length) (baseStart_1032832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1032832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1032832 prefixEnd_1032832 := by exact prefixLift 1032832
  have htrace : WordTrace (prefixWord ++ tailWord_1032832) baseStart_1032832 baseEnd_1032832 := by
    simpa [prefixWord, tailWord_1032832, baseEnd_1032832] using wordTrace_append hprefix tailTrace_1032832
  have hstable : (prefixWord ++ tailWord_1032832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032832).length < 2 ^ (prefixWord ++ tailWord_1032832).sum := by decide
  have hdescent : baseEnd_1032832 < baseStart_1032832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032835 : List Nat := [1, 1, 1, 3, 3, 1, 6, 1, 4]
def baseStart_1032835 : Nat := 118140960795 + 1032835 * 2 ^ 59
def prefixEnd_1032835 : Nat := 4983230072969 + 3 ^ 40 * 1032835 * 2
def baseEnd_1032835 : Nat := 235707018571809672005593

theorem tailTrace_1032835 : CollatzResearch.WordTrace tailWord_1032835 prefixEnd_1032835 235707018571809672005593 := by
  unfold tailWord_1032835
  simp only [CollatzResearch.WordTrace]
  refine ⟨37670587213222664019651959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25113724808815109346434639 37670587213222664019651959)
  ·
    refine ⟨56505880819833996029477939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37670587213222664019651959 56505880819833996029477939)
    ·
      refine ⟨84758821229750994044216909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56505880819833996029477939 84758821229750994044216909)
      ·
        refine ⟨31784557961156622766581341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84758821229750994044216909 31784557961156622766581341)
        ·
          refine ⟨11919209235433733537468003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31784557961156622766581341 11919209235433733537468003)
          ·
            refine ⟨17878813853150600306202005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11919209235433733537468003 17878813853150600306202005)
            ·
              refine ⟨838069399366434389353219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17878813853150600306202005 838069399366434389353219)
              ·
                refine ⟨1257104099049651584029829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838069399366434389353219 1257104099049651584029829)
                ·
                  refine ⟨235707018571809672005593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1257104099049651584029829 235707018571809672005593)
                  ·
                    rfl

theorem cell21_1032835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 4].length) (baseStart_1032835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1032835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1032835 prefixEnd_1032835 := by exact prefixLift 1032835
  have htrace : WordTrace (prefixWord ++ tailWord_1032835) baseStart_1032835 baseEnd_1032835 := by
    simpa [prefixWord, tailWord_1032835, baseEnd_1032835] using wordTrace_append hprefix tailTrace_1032835
  have hstable : (prefixWord ++ tailWord_1032835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032835).length < 2 ^ (prefixWord ++ tailWord_1032835).sum := by decide
  have hdescent : baseEnd_1032835 < baseStart_1032835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032914 : List Nat := [3, 2, 2, 2, 3, 1, 2, 3, 3]
def baseStart_1032914 : Nat := 118140960795 + 1032914 * 2 ^ 59
def prefixEnd_1032914 : Nat := 4983230072969 + 3 ^ 40 * 1032914 * 2
def baseEnd_1032914 : Nat := 235725047448123090188765

theorem tailTrace_1032914 : CollatzResearch.WordTrace tailWord_1032914 prefixEnd_1032914 235725047448123090188765 := by
  unfold tailWord_1032914
  simp only [CollatzResearch.WordTrace]
  refine ⟨9418367144984115127944449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25115645719957640341185197 9418367144984115127944449)
  ·
    refine ⟨7063775358738086345958337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9418367144984115127944449 7063775358738086345958337)
    ·
      refine ⟨5297831519053564759468753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7063775358738086345958337 5297831519053564759468753)
      ·
        refine ⟨3973373639290173569601565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5297831519053564759468753 3973373639290173569601565)
        ·
          refine ⟨1490015114733815088600587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3973373639290173569601565 1490015114733815088600587)
          ·
            refine ⟨2235022672100722632900881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490015114733815088600587 2235022672100722632900881)
            ·
              refine ⟨1676267004075541974675661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2235022672100722632900881 1676267004075541974675661)
              ·
                refine ⟨628600126528328240503373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1676267004075541974675661 628600126528328240503373)
                ·
                  refine ⟨235725047448123090188765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 628600126528328240503373 235725047448123090188765)
                  ·
                    rfl

theorem cell21_1032914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_1032914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1032914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1032914 prefixEnd_1032914 := by exact prefixLift 1032914
  have htrace : WordTrace (prefixWord ++ tailWord_1032914) baseStart_1032914 baseEnd_1032914 := by
    simpa [prefixWord, tailWord_1032914, baseEnd_1032914] using wordTrace_append hprefix tailTrace_1032914
  have hstable : (prefixWord ++ tailWord_1032914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032914).length < 2 ^ (prefixWord ++ tailWord_1032914).sum := by decide
  have hdescent : baseEnd_1032914 < baseStart_1032914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033029 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 6]
def baseStart_1033029 : Nat := 118140960795 + 1033029 * 2 ^ 59
def prefixEnd_1033029 : Nat := 4983230072969 + 3 ^ 40 * 1033029 * 2
def baseEnd_1033029 : Nat := 235751292014908445771863

theorem tailTrace_1033029 : CollatzResearch.WordTrace tailWord_1033029 prefixEnd_1033029 235751292014908445771863 := by
  unfold tailWord_1033029
  simp only [CollatzResearch.WordTrace]
  refine ⟨37677662974519835152214141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25118441983013223434809427 37677662974519835152214141)
  ·
    refine ⟨14129123615444938182080303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37677662974519835152214141 14129123615444938182080303)
    ·
      refine ⟨21193685423167407273120455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14129123615444938182080303 21193685423167407273120455)
      ·
        refine ⟨31790528134751110909680683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21193685423167407273120455 31790528134751110909680683)
        ·
          refine ⟨47685792202126666364521025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31790528134751110909680683 47685792202126666364521025)
          ·
            refine ⟨35764344151594999773390769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47685792202126666364521025 35764344151594999773390769)
            ·
              refine ⟨26823258113696249830043077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35764344151594999773390769 26823258113696249830043077)
              ·
                refine ⟨5029360896318046843133077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26823258113696249830043077 5029360896318046843133077)
                ·
                  refine ⟨235751292014908445771863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5029360896318046843133077 235751292014908445771863)
                  ·
                    rfl

theorem cell21_1033029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_1033029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1033029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1033029 prefixEnd_1033029 := by exact prefixLift 1033029
  have htrace : WordTrace (prefixWord ++ tailWord_1033029) baseStart_1033029 baseEnd_1033029 := by
    simpa [prefixWord, tailWord_1033029, baseEnd_1033029] using wordTrace_append hprefix tailTrace_1033029
  have hstable : (prefixWord ++ tailWord_1033029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033029).length < 2 ^ (prefixWord ++ tailWord_1033029).sum := by decide
  have hdescent : baseEnd_1033029 < baseStart_1033029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033032 : List Nat := [2, 1, 3, 1, 1, 3, 2, 5, 3]
def baseStart_1033032 : Nat := 118140960795 + 1033032 * 2 ^ 59
def prefixEnd_1033032 : Nat := 4983230072969 + 3 ^ 40 * 1033032 * 2
def baseEnd_1033032 : Nat := 235751976655781107221857

theorem tailTrace_1033032 : CollatzResearch.WordTrace tailWord_1033032 prefixEnd_1033032 235751976655781107221857 := by
  unfold tailWord_1033032
  simp only [CollatzResearch.WordTrace]
  refine ⟨18838886196754483332286675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25118514929005977776382233 18838886196754483332286675)
  ·
    refine ⟨28258329295131724998430013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18838886196754483332286675 28258329295131724998430013)
    ·
      refine ⟨10596873485674396874411255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28258329295131724998430013 10596873485674396874411255)
      ·
        refine ⟨15895310228511595311616883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10596873485674396874411255 15895310228511595311616883)
        ·
          refine ⟨23842965342767392967425325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15895310228511595311616883 23842965342767392967425325)
          ·
            refine ⟨8941112003537772362784497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23842965342767392967425325 8941112003537772362784497)
            ·
              refine ⟨6705834002653329272088373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8941112003537772362784497 6705834002653329272088373)
              ·
                refine ⟨628671937748749619258285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6705834002653329272088373 628671937748749619258285)
                ·
                  refine ⟨235751976655781107221857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 628671937748749619258285 235751976655781107221857)
                  ·
                    rfl

theorem cell21_1033032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 3].length) (baseStart_1033032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1033032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1033032 prefixEnd_1033032 := by exact prefixLift 1033032
  have htrace : WordTrace (prefixWord ++ tailWord_1033032) baseStart_1033032 baseEnd_1033032 := by
    simpa [prefixWord, tailWord_1033032, baseEnd_1033032] using wordTrace_append hprefix tailTrace_1033032
  have hstable : (prefixWord ++ tailWord_1033032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033032).length < 2 ^ (prefixWord ++ tailWord_1033032).sum := by decide
  have hdescent : baseEnd_1033032 < baseStart_1033032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033049 : List Nat := [1, 2, 1, 2, 2, 4, 4, 2, 3]
def baseStart_1033049 : Nat := 118140960795 + 1033049 * 2 ^ 59
def prefixEnd_1033049 : Nat := 4983230072969 + 3 ^ 40 * 1033049 * 2
def baseEnd_1033049 : Nat := 235755856287392855438489

theorem tailTrace_1033049 : CollatzResearch.WordTrace tailWord_1033049 prefixEnd_1033049 235755856287392855438489 := by
  unfold tailWord_1033049
  simp only [CollatzResearch.WordTrace]
  refine ⟨37678392434447378567942201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25118928289631585711961467 37678392434447378567942201)
  ·
    refine ⟨28258794325835533925956651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37678392434447378567942201 28258794325835533925956651)
    ·
      refine ⟨42388191488753300888934977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28258794325835533925956651 42388191488753300888934977)
      ·
        refine ⟨31791143616564975666701233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42388191488753300888934977 31791143616564975666701233)
        ·
          refine ⟨23843357712423731750025925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31791143616564975666701233 23843357712423731750025925)
          ·
            refine ⟨4470629571079449703129861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23843357712423731750025925 4470629571079449703129861)
            ·
              refine ⟨838243044577396819336849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4470629571079449703129861 838243044577396819336849)
              ·
                refine ⟨628682283433047614502637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 838243044577396819336849 628682283433047614502637)
                ·
                  refine ⟨235755856287392855438489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 628682283433047614502637 235755856287392855438489)
                  ·
                    rfl

theorem cell21_1033049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 3].length) (baseStart_1033049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1033049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1033049 prefixEnd_1033049 := by exact prefixLift 1033049
  have htrace : WordTrace (prefixWord ++ tailWord_1033049) baseStart_1033049 baseEnd_1033049 := by
    simpa [prefixWord, tailWord_1033049, baseEnd_1033049] using wordTrace_append hprefix tailTrace_1033049
  have hstable : (prefixWord ++ tailWord_1033049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033049).length < 2 ^ (prefixWord ++ tailWord_1033049).sum := by decide
  have hdescent : baseEnd_1033049 < baseStart_1033049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033108 : List Nat := [2, 4, 2, 1, 1, 1, 4, 1, 5]
def baseStart_1033108 : Nat := 118140960795 + 1033108 * 2 ^ 59
def prefixEnd_1033108 : Nat := 4983230072969 + 3 ^ 40 * 1033108 * 2
def baseEnd_1033108 : Nat := 235769320891221863955035

theorem tailTrace_1033108 : CollatzResearch.WordTrace tailWord_1033108 prefixEnd_1033108 235769320891221863955035 := by
  unfold tailWord_1033108
  simp only [CollatzResearch.WordTrace]
  refine ⟨18840272170616815822169989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25120362894155754429559985 18840272170616815822169989)
  ·
    refine ⟨3532551031990652966656873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18840272170616815822169989 3532551031990652966656873)
    ·
      refine ⟨2649413273992989724992655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3532551031990652966656873 2649413273992989724992655)
      ·
        refine ⟨3974119910989484587488983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2649413273992989724992655 3974119910989484587488983)
        ·
          refine ⟨5961179866484226881233475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3974119910989484587488983 5961179866484226881233475)
          ·
            refine ⟨8941769799726340321850213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5961179866484226881233475 8941769799726340321850213)
            ·
              refine ⟨1676581837448688810346915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8941769799726340321850213 1676581837448688810346915)
              ·
                refine ⟨2514872756173033215520373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676581837448688810346915 2514872756173033215520373)
                ·
                  refine ⟨235769320891221863955035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2514872756173033215520373 235769320891221863955035)
                  ·
                    rfl

theorem cell21_1033108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_1033108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1033108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1033108 prefixEnd_1033108 := by exact prefixLift 1033108
  have htrace : WordTrace (prefixWord ++ tailWord_1033108) baseStart_1033108 baseEnd_1033108 := by
    simpa [prefixWord, tailWord_1033108, baseEnd_1033108] using wordTrace_append hprefix tailTrace_1033108
  have hstable : (prefixWord ++ tailWord_1033108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033108).length < 2 ^ (prefixWord ++ tailWord_1033108).sum := by decide
  have hdescent : baseEnd_1033108 < baseStart_1033108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033167 : List Nat := [1, 1, 2, 1, 1, 6, 3, 1, 5]
def baseStart_1033167 : Nat := 118140960795 + 1033167 * 2 ^ 59
def prefixEnd_1033167 : Nat := 4983230072969 + 3 ^ 40 * 1033167 * 2
def baseEnd_1033167 : Nat := 235782785495050872471581

theorem tailTrace_1033167 : CollatzResearch.WordTrace tailWord_1033167 prefixEnd_1033167 235782785495050872471581 := by
  unfold tailWord_1033167
  simp only [CollatzResearch.WordTrace]
  refine ⟨37682696248019884720737755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25121797498679923147158503 37682696248019884720737755)
  ·
    refine ⟨56524044372029827081106633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37682696248019884720737755 56524044372029827081106633)
    ·
      refine ⟨42393033279022370310829975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56524044372029827081106633 42393033279022370310829975)
      ·
        refine ⟨63589549918533555466244963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42393033279022370310829975 63589549918533555466244963)
        ·
          refine ⟨95384324877800333199367445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63589549918533555466244963 95384324877800333199367445)
          ·
            refine ⟨4471140228646890618720349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95384324877800333199367445 4471140228646890618720349)
            ·
              refine ⟨1676677585742583982020131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4471140228646890618720349 1676677585742583982020131)
              ·
                refine ⟨2515016378613875973030197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676677585742583982020131 2515016378613875973030197)
                ·
                  refine ⟨235782785495050872471581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2515016378613875973030197 235782785495050872471581)
                  ·
                    rfl

theorem cell21_1033167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 5].length) (baseStart_1033167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1033167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1033167 prefixEnd_1033167 := by exact prefixLift 1033167
  have htrace : WordTrace (prefixWord ++ tailWord_1033167) baseStart_1033167 baseEnd_1033167 := by
    simpa [prefixWord, tailWord_1033167, baseEnd_1033167] using wordTrace_append hprefix tailTrace_1033167
  have hstable : (prefixWord ++ tailWord_1033167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033167).length < 2 ^ (prefixWord ++ tailWord_1033167).sum := by decide
  have hdescent : baseEnd_1033167 < baseStart_1033167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033173 : List Nat := [1, 3, 2, 3, 4, 1, 2, 1, 4]
def baseStart_1033173 : Nat := 118140960795 + 1033173 * 2 ^ 59
def prefixEnd_1033173 : Nat := 4983230072969 + 3 ^ 40 * 1033173 * 2
def baseEnd_1033173 : Nat := 235784154776796195371569

theorem tailTrace_1033173 : CollatzResearch.WordTrace tailWord_1033173 prefixEnd_1033173 235784154776796195371569 := by
  unfold tailWord_1033173
  simp only [CollatzResearch.WordTrace]
  refine ⟨37682915085998147745456173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25121943390665431830304115 37682915085998147745456173)
  ·
    refine ⟨14131093157249305404546065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37682915085998147745456173 14131093157249305404546065)
    ·
      refine ⟨10598319867936979053409549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14131093157249305404546065 10598319867936979053409549)
      ·
        refine ⟨3974369950476367145028581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10598319867936979053409549 3974369950476367145028581)
        ·
          refine ⟨745194365714318839692859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3974369950476367145028581 745194365714318839692859)
          ·
            refine ⟨1117791548571478259539289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745194365714318839692859 1117791548571478259539289)
            ·
              refine ⟨838343661428608694654467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1117791548571478259539289 838343661428608694654467)
              ·
                refine ⟨1257515492142913041981701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838343661428608694654467 1257515492142913041981701)
                ·
                  refine ⟨235784154776796195371569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1257515492142913041981701 235784154776796195371569)
                  ·
                    rfl

theorem cell21_1033173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_1033173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1033173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1033173 prefixEnd_1033173 := by exact prefixLift 1033173
  have htrace : WordTrace (prefixWord ++ tailWord_1033173) baseStart_1033173 baseEnd_1033173 := by
    simpa [prefixWord, tailWord_1033173, baseEnd_1033173] using wordTrace_append hprefix tailTrace_1033173
  have hstable : (prefixWord ++ tailWord_1033173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033173).length < 2 ^ (prefixWord ++ tailWord_1033173).sum := by decide
  have hdescent : baseEnd_1033173 < baseStart_1033173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033204 : List Nat := [2, 6, 2, 1, 2, 8]
def baseStart_1033204 : Nat := 118140960795 + 1033204 * 2 ^ 59
def prefixEnd_1033204 : Nat := 4983230072969 + 3 ^ 40 * 1033204 * 2
def baseEnd_1033204 : Nat := 8733008496264704827957

theorem tailTrace_1033204 : CollatzResearch.WordTrace tailWord_1033204 prefixEnd_1033204 8733008496264704827957 := by
  unfold tailWord_1033204
  simp only [CollatzResearch.WordTrace]
  refine ⟨18842022874442920019917333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25122697165923893359889777 18842022874442920019917333)
  ·
    refine ⟨883219822239511875933625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18842022874442920019917333 883219822239511875933625)
    ·
      refine ⟨662414866679633906950219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 883219822239511875933625 662414866679633906950219)
      ·
        refine ⟨993622300019450860425329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662414866679633906950219 993622300019450860425329)
        ·
          refine ⟨745216725014588145318997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 993622300019450860425329 745216725014588145318997)
          ·
            refine ⟨8733008496264704827957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 745216725014588145318997 8733008496264704827957)
            ·
              rfl

theorem cell21_1033204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 8].length) (baseStart_1033204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1033204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1033204 prefixEnd_1033204 := by exact prefixLift 1033204
  have htrace : WordTrace (prefixWord ++ tailWord_1033204) baseStart_1033204 baseEnd_1033204 := by
    simpa [prefixWord, tailWord_1033204, baseEnd_1033204] using wordTrace_append hprefix tailTrace_1033204
  have hstable : (prefixWord ++ tailWord_1033204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033204).length < 2 ^ (prefixWord ++ tailWord_1033204).sum := by decide
  have hdescent : baseEnd_1033204 < baseStart_1033204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033260 : List Nat := [2, 2, 1, 1, 1, 2, 6, 3, 3]
def baseStart_1033260 : Nat := 118140960795 + 1033260 * 2 ^ 59
def prefixEnd_1033260 : Nat := 4983230072969 + 3 ^ 40 * 1033260 * 2
def baseEnd_1033260 : Nat := 235804009362103377421391

theorem tailTrace_1033260 : CollatzResearch.WordTrace tailWord_1033260 prefixEnd_1033260 235804009362103377421391 := by
  unfold tailWord_1033260
  simp only [CollatzResearch.WordTrace]
  refine ⟨18843044118341480801936617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25124058824455307735915489 18843044118341480801936617)
  ·
    refine ⟨14132283088756110601452463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18843044118341480801936617 14132283088756110601452463)
    ·
      refine ⟨21198424633134165902178695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14132283088756110601452463 21198424633134165902178695)
      ·
        refine ⟨31797636949701248853268043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21198424633134165902178695 31797636949701248853268043)
        ·
          refine ⟨47696455424551873279902065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31797636949701248853268043 47696455424551873279902065)
          ·
            refine ⟨35772341568413904959926549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47696455424551873279902065 35772341568413904959926549)
            ·
              refine ⟨1676828511019401794996557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35772341568413904959926549 1676828511019401794996557)
              ·
                refine ⟨628810691632275673123709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1676828511019401794996557 628810691632275673123709)
                ·
                  refine ⟨235804009362103377421391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 628810691632275673123709 235804009362103377421391)
                  ·
                    rfl

theorem cell21_1033260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_1033260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1033260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1033260 prefixEnd_1033260 := by exact prefixLift 1033260
  have htrace : WordTrace (prefixWord ++ tailWord_1033260) baseStart_1033260 baseEnd_1033260 := by
    simpa [prefixWord, tailWord_1033260, baseEnd_1033260] using wordTrace_append hprefix tailTrace_1033260
  have hstable : (prefixWord ++ tailWord_1033260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033260).length < 2 ^ (prefixWord ++ tailWord_1033260).sum := by decide
  have hdescent : baseEnd_1033260 < baseStart_1033260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033274 : List Nat := [3, 1, 1, 1, 3, 1, 5, 2, 4]
def baseStart_1033274 : Nat := 118140960795 + 1033274 * 2 ^ 59
def prefixEnd_1033274 : Nat := 4983230072969 + 3 ^ 40 * 1033274 * 2
def baseEnd_1033274 : Nat := 235807204352842464188029

theorem tailTrace_1033274 : CollatzResearch.WordTrace tailWord_1033274 prefixEnd_1033274 235807204352842464188029 := by
  unfold tailWord_1033274
  simp only [CollatzResearch.WordTrace]
  refine ⟨9421649714658060498720719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25124399239088161329921917 9421649714658060498720719)
  ·
    refine ⟨14132474571987090748081079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9421649714658060498720719 14132474571987090748081079)
    ·
      refine ⟨21198711857980636122121619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14132474571987090748081079 21198711857980636122121619)
      ·
        refine ⟨31798067786970954183182429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21198711857980636122121619 31798067786970954183182429)
        ·
          refine ⟨11924275420114107818693411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31798067786970954183182429 11924275420114107818693411)
          ·
            refine ⟨17886413130171161728040117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11924275420114107818693411 17886413130171161728040117)
            ·
              refine ⟨1676851230953546412003761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17886413130171161728040117 1676851230953546412003761)
              ·
                refine ⟨1257638423215159809002821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1676851230953546412003761 1257638423215159809002821)
                ·
                  refine ⟨235807204352842464188029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1257638423215159809002821 235807204352842464188029)
                  ·
                    rfl

theorem cell21_1033274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_1033274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1033274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1033274 prefixEnd_1033274 := by exact prefixLift 1033274
  have htrace : WordTrace (prefixWord ++ tailWord_1033274) baseStart_1033274 baseEnd_1033274 := by
    simpa [prefixWord, tailWord_1033274, baseEnd_1033274] using wordTrace_append hprefix tailTrace_1033274
  have hstable : (prefixWord ++ tailWord_1033274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033274).length < 2 ^ (prefixWord ++ tailWord_1033274).sum := by decide
  have hdescent : baseEnd_1033274 < baseStart_1033274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033412 : List Nat := [2, 3, 3, 1, 3, 1, 1, 2, 5]
def baseStart_1033412 : Nat := 118140960795 + 1033412 * 2 ^ 59
def prefixEnd_1033412 : Nat := 4983230072969 + 3 ^ 40 * 1033412 * 2
def baseEnd_1033412 : Nat := 235838697832984890887747

theorem tailTrace_1033412 : CollatzResearch.WordTrace tailWord_1033412 prefixEnd_1033412 235838697832984890887747 := by
  unfold tailWord_1033412
  simp only [CollatzResearch.WordTrace]
  refine ⟨18845816066066145781703245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25127754754754861042270993 18845816066066145781703245)
  ·
    refine ⟨7067181024774804668138717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18845816066066145781703245 7067181024774804668138717)
    ·
      refine ⟨2650192884290551750552019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7067181024774804668138717 2650192884290551750552019)
      ·
        refine ⟨3975289326435827625828029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2650192884290551750552019 3975289326435827625828029)
        ·
          refine ⟨1490733497413435359685511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3975289326435827625828029 1490733497413435359685511)
          ·
            refine ⟨2236100246120153039528267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490733497413435359685511 2236100246120153039528267)
            ·
              refine ⟨3354150369180229559292401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2236100246120153039528267 3354150369180229559292401)
              ·
                refine ⟨2515612776885172169469301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3354150369180229559292401 2515612776885172169469301)
                ·
                  refine ⟨235838697832984890887747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2515612776885172169469301 235838697832984890887747)
                  ·
                    rfl

theorem cell21_1033412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_1033412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1033412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1033412 prefixEnd_1033412 := by exact prefixLift 1033412
  have htrace : WordTrace (prefixWord ++ tailWord_1033412) baseStart_1033412 baseEnd_1033412 := by
    simpa [prefixWord, tailWord_1033412, baseEnd_1033412] using wordTrace_append hprefix tailTrace_1033412
  have hstable : (prefixWord ++ tailWord_1033412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033412).length < 2 ^ (prefixWord ++ tailWord_1033412).sum := by decide
  have hdescent : baseEnd_1033412 < baseStart_1033412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033429 : List Nat := [1, 3, 2, 4, 1, 2, 2, 3, 3]
def baseStart_1033429 : Nat := 118140960795 + 1033429 * 2 ^ 59
def prefixEnd_1033429 : Nat := 4983230072969 + 3 ^ 40 * 1033429 * 2
def baseEnd_1033429 : Nat := 235842577464596639104379

theorem tailTrace_1033429 : CollatzResearch.WordTrace tailWord_1033429 prefixEnd_1033429 235842577464596639104379 := by
  unfold tailWord_1033429
  simp only [CollatzResearch.WordTrace]
  refine ⟨37692252173070703466775341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25128168115380468977850227 37692252173070703466775341)
  ·
    refine ⟨14134594564901513800040753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37692252173070703466775341 14134594564901513800040753)
    ·
      refine ⟨10600945923676135350030565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14134594564901513800040753 10600945923676135350030565)
      ·
        refine ⟨1987677360689275378130731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10600945923676135350030565 1987677360689275378130731)
        ·
          refine ⟨2981516041033913067196097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1987677360689275378130731 2981516041033913067196097)
          ·
            refine ⟨2236137030775434800397073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2981516041033913067196097 2236137030775434800397073)
            ·
              refine ⟨1677102773081576100297805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2236137030775434800397073 1677102773081576100297805)
              ·
                refine ⟨628913539905591037611677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1677102773081576100297805 628913539905591037611677)
                ·
                  refine ⟨235842577464596639104379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 628913539905591037611677 235842577464596639104379)
                  ·
                    rfl

theorem cell21_1033429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_1033429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1033429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1033429 prefixEnd_1033429 := by exact prefixLift 1033429
  have htrace : WordTrace (prefixWord ++ tailWord_1033429) baseStart_1033429 baseEnd_1033429 := by
    simpa [prefixWord, tailWord_1033429, baseEnd_1033429] using wordTrace_append hprefix tailTrace_1033429
  have hstable : (prefixWord ++ tailWord_1033429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033429).length < 2 ^ (prefixWord ++ tailWord_1033429).sum := by decide
  have hdescent : baseEnd_1033429 < baseStart_1033429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033530 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 7]
def baseStart_1033530 : Nat := 118140960795 + 1033530 * 2 ^ 59
def prefixEnd_1033530 : Nat := 4983230072969 + 3 ^ 40 * 1033530 * 2
def baseEnd_1033530 : Nat := 235865627040642907920839

theorem tailTrace_1033530 : CollatzResearch.WordTrace tailWord_1033530 prefixEnd_1033530 235865627040642907920839 := by
  unfold tailWord_1033530
  simp only [CollatzResearch.WordTrace]
  refine ⟨9423983986426199429050511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25130623963803198477468029 9423983986426199429050511)
  ·
    refine ⟨14135975979639299143575767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9423983986426199429050511 14135975979639299143575767)
    ·
      refine ⟨21203963969458948715363651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14135975979639299143575767 21203963969458948715363651)
      ·
        refine ⟨31805945954188423073045477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21203963969458948715363651 31805945954188423073045477)
        ·
          refine ⟨5963614866410329326196027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31805945954188423073045477 5963614866410329326196027)
          ·
            refine ⟨8945422299615493989294041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5963614866410329326196027 8945422299615493989294041)
            ·
              refine ⟨6709066724711620491970531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8945422299615493989294041 6709066724711620491970531)
              ·
                refine ⟨10063600087067430737955797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6709066724711620491970531 10063600087067430737955797)
                ·
                  refine ⟨235865627040642907920839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10063600087067430737955797 235865627040642907920839)
                  ·
                    rfl

theorem cell21_1033530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_1033530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1033530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1033530 prefixEnd_1033530 := by exact prefixLift 1033530
  have htrace : WordTrace (prefixWord ++ tailWord_1033530) baseStart_1033530 baseEnd_1033530 := by
    simpa [prefixWord, tailWord_1033530, baseEnd_1033530] using wordTrace_append hprefix tailTrace_1033530
  have hstable : (prefixWord ++ tailWord_1033530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033530).length < 2 ^ (prefixWord ++ tailWord_1033530).sum := by decide
  have hdescent : baseEnd_1033530 < baseStart_1033530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033561 : List Nat := [1, 2, 1, 2, 2, 2, 3, 4, 4]
def baseStart_1033561 : Nat := 118140960795 + 1033561 * 2 ^ 59
def prefixEnd_1033561 : Nat := 4983230072969 + 3 ^ 40 * 1033561 * 2
def baseEnd_1033561 : Nat := 235872701662993742904109

theorem tailTrace_1033561 : CollatzResearch.WordTrace tailWord_1033561 prefixEnd_1033561 235872701662993742904109 := by
  unfold tailWord_1033561
  simp only [CollatzResearch.WordTrace]
  refine ⟨37697066608592490010580537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25131377739061660007053691 37697066608592490010580537)
  ·
    refine ⟨28272799956444367507935403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37697066608592490010580537 28272799956444367507935403)
    ·
      refine ⟨42409199934666551261903105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28272799956444367507935403 42409199934666551261903105)
      ·
        refine ⟨31806899950999913446427329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42409199934666551261903105 31806899950999913446427329)
        ·
          refine ⟨23855174963249935084820497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31806899950999913446427329 23855174963249935084820497)
          ·
            refine ⟨17891381222437451313615373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23855174963249935084820497 17891381222437451313615373)
            ·
              refine ⟨6709267958414044242605765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17891381222437451313615373 6709267958414044242605765)
              ·
                refine ⟨1257987742202633295488581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6709267958414044242605765 1257987742202633295488581)
                ·
                  refine ⟨235872701662993742904109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1257987742202633295488581 235872701662993742904109)
                  ·
                    rfl

theorem cell21_1033561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 4].length) (baseStart_1033561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1033561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1033561 prefixEnd_1033561 := by exact prefixLift 1033561
  have htrace : WordTrace (prefixWord ++ tailWord_1033561) baseStart_1033561 baseEnd_1033561 := by
    simpa [prefixWord, tailWord_1033561, baseEnd_1033561] using wordTrace_append hprefix tailTrace_1033561
  have hstable : (prefixWord ++ tailWord_1033561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033561).length < 2 ^ (prefixWord ++ tailWord_1033561).sum := by decide
  have hdescent : baseEnd_1033561 < baseStart_1033561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033657 : List Nat := [1, 2, 1, 4, 4, 2, 1, 3, 3]
def baseStart_1033657 : Nat := 118140960795 + 1033657 * 2 ^ 59
def prefixEnd_1033657 : Nat := 4983230072969 + 3 ^ 40 * 1033657 * 2
def baseEnd_1033657 : Nat := 235894610170918909303913

theorem tailTrace_1033657 : CollatzResearch.WordTrace tailWord_1033657 prefixEnd_1033657 235894610170918909303913 := by
  unfold tailWord_1033657
  simp only [CollatzResearch.WordTrace]
  refine ⟨37700568016244698406075225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25133712010829798937383483 37700568016244698406075225)
  ·
    refine ⟨28275426012183523804556419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37700568016244698406075225 28275426012183523804556419)
    ·
      refine ⟨42413139018275285706834629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28275426012183523804556419 42413139018275285706834629)
      ·
        refine ⟨7952463565926616070031493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42413139018275285706834629 7952463565926616070031493)
        ·
          refine ⟨1491086918611240513130905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7952463565926616070031493 1491086918611240513130905)
          ·
            refine ⟨1118315188958430384848179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1491086918611240513130905 1118315188958430384848179)
            ·
              refine ⟨1677472783437645577272269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118315188958430384848179 1677472783437645577272269)
              ·
                refine ⟨629052293789117091477101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1677472783437645577272269 629052293789117091477101)
                ·
                  refine ⟨235894610170918909303913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 629052293789117091477101 235894610170918909303913)
                  ·
                    rfl

theorem cell21_1033657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 3].length) (baseStart_1033657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1033657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1033657 prefixEnd_1033657 := by exact prefixLift 1033657
  have htrace : WordTrace (prefixWord ++ tailWord_1033657) baseStart_1033657 baseEnd_1033657 := by
    simpa [prefixWord, tailWord_1033657, baseEnd_1033657] using wordTrace_append hprefix tailTrace_1033657
  have hstable : (prefixWord ++ tailWord_1033657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033657).length < 2 ^ (prefixWord ++ tailWord_1033657).sum := by decide
  have hdescent : baseEnd_1033657 < baseStart_1033657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033668 : List Nat := [2, 3, 3, 2, 1, 1, 9]
def baseStart_1033668 : Nat := 118140960795 + 1033668 * 2 ^ 59
def prefixEnd_1033668 : Nat := 4983230072969 + 3 ^ 40 * 1033668 * 2
def baseEnd_1033668 : Nat := 26210791168976148291173

theorem tailTrace_1033668 : CollatzResearch.WordTrace tailWord_1033668 prefixEnd_1033668 26210791168976148291173 := by
  unfold tailWord_1033668
  simp only [CollatzResearch.WordTrace]
  refine ⟨18850484609602423642362829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25133979479469898189817105 18850484609602423642362829)
  ·
    refine ⟨7068931728600908865886061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18850484609602423642362829 7068931728600908865886061)
    ·
      refine ⟨2650849398225340824707273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7068931728600908865886061 2650849398225340824707273)
      ·
        refine ⟨1988137048669005618530455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2650849398225340824707273 1988137048669005618530455)
        ·
          refine ⟨2982205573003508427795683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1988137048669005618530455 2982205573003508427795683)
          ·
            refine ⟨4473308359505262641693525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2982205573003508427795683 4473308359505262641693525)
            ·
              refine ⟨26210791168976148291173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4473308359505262641693525 26210791168976148291173)
              ·
                rfl

theorem cell21_1033668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 9].length) (baseStart_1033668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1033668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1033668 prefixEnd_1033668 := by exact prefixLift 1033668
  have htrace : WordTrace (prefixWord ++ tailWord_1033668) baseStart_1033668 baseEnd_1033668 := by
    simpa [prefixWord, tailWord_1033668, baseEnd_1033668] using wordTrace_append hprefix tailTrace_1033668
  have hstable : (prefixWord ++ tailWord_1033668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033668).length < 2 ^ (prefixWord ++ tailWord_1033668).sum := by decide
  have hdescent : baseEnd_1033668 < baseStart_1033668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033696 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 8]
def baseStart_1033696 : Nat := 118140960795 + 1033696 * 2 ^ 59
def prefixEnd_1033696 : Nat := 4983230072969 + 3 ^ 40 * 1033696 * 2
def baseEnd_1033696 : Nat := 235903510502263508153833

theorem tailTrace_1033696 : CollatzResearch.WordTrace tailWord_1033696 prefixEnd_1033696 235903510502263508153833 := by
  unfold tailWord_1033696
  simp only [CollatzResearch.WordTrace]
  refine ⟨18850995231551704033372471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25134660308735605377829961 18850995231551704033372471)
  ·
    refine ⟨28276492847327556050058707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18850995231551704033372471 28276492847327556050058707)
    ·
      refine ⟨42414739270991334075088061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28276492847327556050058707 42414739270991334075088061)
      ·
        refine ⟨15905527226621750278158023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42414739270991334075088061 15905527226621750278158023)
        ·
          refine ⟨23858290839932625417237035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15905527226621750278158023 23858290839932625417237035)
          ·
            refine ⟨35787436259898938125855553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23858290839932625417237035 35787436259898938125855553)
            ·
              refine ⟨26840577194924203594391665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35787436259898938125855553 26840577194924203594391665)
              ·
                refine ⟨20130432896193152695793749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26840577194924203594391665 20130432896193152695793749)
                ·
                  refine ⟨235903510502263508153833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20130432896193152695793749 235903510502263508153833)
                  ·
                    rfl

theorem cell21_1033696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_1033696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1033696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1033696 prefixEnd_1033696 := by exact prefixLift 1033696
  have htrace : WordTrace (prefixWord ++ tailWord_1033696) baseStart_1033696 baseEnd_1033696 := by
    simpa [prefixWord, tailWord_1033696, baseEnd_1033696] using wordTrace_append hprefix tailTrace_1033696
  have hstable : (prefixWord ++ tailWord_1033696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033696).length < 2 ^ (prefixWord ++ tailWord_1033696).sum := by decide
  have hdescent : baseEnd_1033696 < baseStart_1033696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033820 : List Nat := [2, 2, 4, 1, 2, 2, 1, 7]
def baseStart_1033820 : Nat := 118140960795 + 1033820 * 2 ^ 59
def prefixEnd_1033820 : Nat := 4983230072969 + 3 ^ 40 * 1033820 * 2
def baseEnd_1033820 : Nat := 78643936330555616028971

theorem tailTrace_1033820 : CollatzResearch.WordTrace tailWord_1033820 prefixEnd_1033820 78643936330555616028971 := by
  unfold tailWord_1033820
  simp only [CollatzResearch.WordTrace]
  refine ⟨18853256557327088622129457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25137675409769451496172609 18853256557327088622129457)
  ·
    refine ⟨14139942417995316466597093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18853256557327088622129457 14139942417995316466597093)
    ·
      refine ⟨2651239203374121837486955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14139942417995316466597093 2651239203374121837486955)
      ·
        refine ⟨3976858805061182756230433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2651239203374121837486955 3976858805061182756230433)
        ·
          refine ⟨2982644103795887067172825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3976858805061182756230433 2982644103795887067172825)
          ·
            refine ⟨2236983077846915300379619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2982644103795887067172825 2236983077846915300379619)
            ·
              refine ⟨3355474616770372950569429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2236983077846915300379619 3355474616770372950569429)
              ·
                refine ⟨78643936330555616028971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3355474616770372950569429 78643936330555616028971)
                ·
                  rfl

theorem cell21_1033820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 7].length) (baseStart_1033820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1033820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1033820 prefixEnd_1033820 := by exact prefixLift 1033820
  have htrace : WordTrace (prefixWord ++ tailWord_1033820) baseStart_1033820 baseEnd_1033820 := by
    simpa [prefixWord, tailWord_1033820, baseEnd_1033820] using wordTrace_append hprefix tailTrace_1033820
  have hstable : (prefixWord ++ tailWord_1033820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033820).length < 2 ^ (prefixWord ++ tailWord_1033820).sum := by decide
  have hdescent : baseEnd_1033820 < baseStart_1033820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033837 : List Nat := [1, 5, 1, 1, 5, 1, 7]
def baseStart_1033837 : Nat := 118140960795 + 1033837 * 2 ^ 59
def prefixEnd_1033837 : Nat := 4983230072969 + 3 ^ 40 * 1033837 * 2
def baseEnd_1033837 : Nat := 26215076513697621811505

theorem tailTrace_1033837 : CollatzResearch.WordTrace tailWord_1033837 prefixEnd_1033837 26215076513697621811505 := by
  unfold tailWord_1033837
  simp only [CollatzResearch.WordTrace]
  refine ⟨37707133155592589147627765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25138088770395059431751843 37707133155592589147627765)
  ·
    refine ⟨3535043733336805232590103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37707133155592589147627765 3535043733336805232590103)
    ·
      refine ⟨5302565600005207848885155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3535043733336805232590103 5302565600005207848885155)
      ·
        refine ⟨7953848400007811773327733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5302565600005207848885155 7953848400007811773327733)
        ·
          refine ⟨745673287500732353749475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7953848400007811773327733 745673287500732353749475)
          ·
            refine ⟨1118509931251098530624213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745673287500732353749475 1118509931251098530624213)
            ·
              refine ⟨26215076513697621811505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1118509931251098530624213 26215076513697621811505)
              ·
                rfl

theorem cell21_1033837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 7].length) (baseStart_1033837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1033837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1033837 prefixEnd_1033837 := by exact prefixLift 1033837
  have htrace : WordTrace (prefixWord ++ tailWord_1033837) baseStart_1033837 baseEnd_1033837 := by
    simpa [prefixWord, tailWord_1033837, baseEnd_1033837] using wordTrace_append hprefix tailTrace_1033837
  have hstable : (prefixWord ++ tailWord_1033837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033837).length < 2 ^ (prefixWord ++ tailWord_1033837).sum := by decide
  have hdescent : baseEnd_1033837 < baseStart_1033837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033879 : List Nat := [1, 1, 3, 3, 2, 2, 2, 7]
def baseStart_1033879 : Nat := 118140960795 + 1033879 * 2 ^ 59
def prefixEnd_1033879 : Nat := 4983230072969 + 3 ^ 40 * 1033879 * 2
def baseEnd_1033879 : Nat := 78648424531831952201153

theorem tailTrace_1033879 : CollatzResearch.WordTrace tailWord_1033879 prefixEnd_1033879 78648424531831952201153 := by
  unfold tailWord_1033879
  simp only [CollatzResearch.WordTrace]
  refine ⟨37708665021440430320656691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25139110014293620213771127 37708665021440430320656691)
  ·
    refine ⟨56562997532160645480985037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37708665021440430320656691 56562997532160645480985037)
    ·
      refine ⟨21211124074560242055369389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56562997532160645480985037 21211124074560242055369389)
      ·
        refine ⟨7954171527960090770763521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21211124074560242055369389 7954171527960090770763521)
        ·
          refine ⟨5965628645970068078072641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7954171527960090770763521 5965628645970068078072641)
          ·
            refine ⟨4474221484477551058554481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5965628645970068078072641 4474221484477551058554481)
            ·
              refine ⟨3355666113358163293915861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4474221484477551058554481 3355666113358163293915861)
              ·
                refine ⟨78648424531831952201153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3355666113358163293915861 78648424531831952201153)
                ·
                  rfl

theorem cell21_1033879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 7].length) (baseStart_1033879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1033879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1033879 prefixEnd_1033879 := by exact prefixLift 1033879
  have htrace : WordTrace (prefixWord ++ tailWord_1033879) baseStart_1033879 baseEnd_1033879 := by
    simpa [prefixWord, tailWord_1033879, baseEnd_1033879] using wordTrace_append hprefix tailTrace_1033879
  have hstable : (prefixWord ++ tailWord_1033879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033879).length < 2 ^ (prefixWord ++ tailWord_1033879).sum := by decide
  have hdescent : baseEnd_1033879 < baseStart_1033879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034034 : List Nat := [3, 2, 1, 1, 3, 2, 4, 1, 4]
def baseStart_1034034 : Nat := 118140960795 + 1034034 * 2 ^ 59
def prefixEnd_1034034 : Nat := 4983230072969 + 3 ^ 40 * 1034034 * 2
def baseEnd_1034034 : Nat := 235980646707250031519809

theorem tailTrace_1034034 : CollatzResearch.WordTrace tailWord_1034034 prefixEnd_1034034 235980646707250031519809 := by
  unfold tailWord_1034034
  simp only [CollatzResearch.WordTrace]
  refine ⟨9428579583969722948137289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25142878890585927861699437 9428579583969722948137289)
  ·
    refine ⟨7071434687977292211102967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9428579583969722948137289 7071434687977292211102967)
    ·
      refine ⟨10607152031965938316654451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7071434687977292211102967 10607152031965938316654451)
      ·
        refine ⟨15910728047948907474981677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10607152031965938316654451 15910728047948907474981677)
        ·
          refine ⟨5966523017980840303118129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15910728047948907474981677 5966523017980840303118129)
          ·
            refine ⟨4474892263485630227338597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5966523017980840303118129 4474892263485630227338597)
            ·
              refine ⟨839042299403555667625987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4474892263485630227338597 839042299403555667625987)
              ·
                refine ⟨1258563449105333501438981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 839042299403555667625987 1258563449105333501438981)
                ·
                  refine ⟨235980646707250031519809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1258563449105333501438981 235980646707250031519809)
                  ·
                    rfl

theorem cell21_1034034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_1034034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1034034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1034034 prefixEnd_1034034 := by exact prefixLift 1034034
  have htrace : WordTrace (prefixWord ++ tailWord_1034034) baseStart_1034034 baseEnd_1034034 := by
    simpa [prefixWord, tailWord_1034034, baseEnd_1034034] using wordTrace_append hprefix tailTrace_1034034
  have hstable : (prefixWord ++ tailWord_1034034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034034).length < 2 ^ (prefixWord ++ tailWord_1034034).sum := by decide
  have hdescent : baseEnd_1034034 < baseStart_1034034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034079 : List Nat := [1, 1, 2, 3, 1, 5, 1, 4, 3]
def baseStart_1034079 : Nat := 118140960795 + 1034079 * 2 ^ 59
def prefixEnd_1034079 : Nat := 4983230072969 + 3 ^ 40 * 1034079 * 2
def baseEnd_1034079 : Nat := 235990916320339953269717

theorem tailTrace_1034079 : CollatzResearch.WordTrace tailWord_1034079 prefixEnd_1034079 235990916320339953269717 := by
  unfold tailWord_1034079
  simp only [CollatzResearch.WordTrace]
  refine ⟨37715959620715864477937291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25143973080477242985291527 37715959620715864477937291)
  ·
    refine ⟨56573939431073796716905937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37715959620715864477937291 56573939431073796716905937)
    ·
      refine ⟨42430454573305347537679453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56573939431073796716905937 42430454573305347537679453)
      ·
        refine ⟨15911420464989505326629795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42430454573305347537679453 15911420464989505326629795)
        ·
          refine ⟨23867130697484257989944693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15911420464989505326629795 23867130697484257989944693)
          ·
            refine ⟨2237543502889149186557315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23867130697484257989944693 2237543502889149186557315)
            ·
              refine ⟨3356315254333723779835973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2237543502889149186557315 3356315254333723779835973)
              ·
                refine ⟨629309110187573208719245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3356315254333723779835973 629309110187573208719245)
                ·
                  refine ⟨235990916320339953269717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 629309110187573208719245 235990916320339953269717)
                  ·
                    rfl

theorem cell21_1034079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 3].length) (baseStart_1034079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1034079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1034079 prefixEnd_1034079 := by exact prefixLift 1034079
  have htrace : WordTrace (prefixWord ++ tailWord_1034079) baseStart_1034079 baseEnd_1034079 := by
    simpa [prefixWord, tailWord_1034079, baseEnd_1034079] using wordTrace_append hprefix tailTrace_1034079
  have hstable : (prefixWord ++ tailWord_1034079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034079).length < 2 ^ (prefixWord ++ tailWord_1034079).sum := by decide
  have hdescent : baseEnd_1034079 < baseStart_1034079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034093 : List Nat := [1, 5, 1, 1, 1, 1, 4, 3, 4]
def baseStart_1034093 : Nat := 118140960795 + 1034093 * 2 ^ 59
def prefixEnd_1034093 : Nat := 4983230072969 + 3 ^ 40 * 1034093 * 2
def baseEnd_1034093 : Nat := 235994111311079040036355

theorem tailTrace_1034093 : CollatzResearch.WordTrace tailWord_1034093 prefixEnd_1034093 235994111311079040036355 := by
  unfold tailWord_1034093
  simp only [CollatzResearch.WordTrace]
  refine ⟨37716470242665144868946933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25144313495110096579297955 37716470242665144868946933)
  ·
    refine ⟨3535919085249857331463775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37716470242665144868946933 3535919085249857331463775)
    ·
      refine ⟨5303878627874785997195663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3535919085249857331463775 5303878627874785997195663)
      ·
        refine ⟨7955817941812178995793495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5303878627874785997195663 7955817941812178995793495)
        ·
          refine ⟨11933726912718268493690243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7955817941812178995793495 11933726912718268493690243)
          ·
            refine ⟨17900590369077402740535365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11933726912718268493690243 17900590369077402740535365)
            ·
              refine ⟨3356360694202013013850381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17900590369077402740535365 3356360694202013013850381)
              ·
                refine ⟨1258635260325754880193893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3356360694202013013850381 1258635260325754880193893)
                ·
                  refine ⟨235994111311079040036355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1258635260325754880193893 235994111311079040036355)
                  ·
                    rfl

theorem cell21_1034093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_1034093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1034093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1034093 prefixEnd_1034093 := by exact prefixLift 1034093
  have htrace : WordTrace (prefixWord ++ tailWord_1034093) baseStart_1034093 baseEnd_1034093 := by
    simpa [prefixWord, tailWord_1034093, baseEnd_1034093] using wordTrace_append hprefix tailTrace_1034093
  have hstable : (prefixWord ++ tailWord_1034093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034093).length < 2 ^ (prefixWord ++ tailWord_1034093).sum := by decide
  have hdescent : baseEnd_1034093 < baseStart_1034093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034113 : List Nat := [1, 2, 4, 4, 1, 1, 2, 3, 3]
def baseStart_1034113 : Nat := 118140960795 + 1034113 * 2 ^ 59
def prefixEnd_1034113 : Nat := 4983230072969 + 3 ^ 40 * 1034113 * 2
def baseEnd_1034113 : Nat := 235998675583563449702981

theorem tailTrace_1034113 : CollatzResearch.WordTrace tailWord_1034113 prefixEnd_1034113 235998675583563449702981 := by
  unfold tailWord_1034113
  simp only [CollatzResearch.WordTrace]
  refine ⟨37717199702592688284674993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25144799801728458856449995 37717199702592688284674993)
  ·
    refine ⟨28287899776944516213506245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37717199702592688284674993 28287899776944516213506245)
    ·
      refine ⟨5303981208177096790032421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28287899776944516213506245 5303981208177096790032421)
      ·
        refine ⟨994496476533205648131079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5303981208177096790032421 994496476533205648131079)
        ·
          refine ⟨1491744714799808472196619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994496476533205648131079 1491744714799808472196619)
          ·
            refine ⟨2237617072199712708294929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491744714799808472196619 2237617072199712708294929)
            ·
              refine ⟨1678212804149784531221197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2237617072199712708294929 1678212804149784531221197)
              ·
                refine ⟨629329801556169199207949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1678212804149784531221197 629329801556169199207949)
                ·
                  refine ⟨235998675583563449702981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 629329801556169199207949 235998675583563449702981)
                  ·
                    rfl

theorem cell21_1034113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 3].length) (baseStart_1034113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1034113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1034113 prefixEnd_1034113 := by exact prefixLift 1034113
  have htrace : WordTrace (prefixWord ++ tailWord_1034113) baseStart_1034113 baseEnd_1034113 := by
    simpa [prefixWord, tailWord_1034113, baseEnd_1034113] using wordTrace_append hprefix tailTrace_1034113
  have hstable : (prefixWord ++ tailWord_1034113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034113).length < 2 ^ (prefixWord ++ tailWord_1034113).sum := by decide
  have hdescent : baseEnd_1034113 < baseStart_1034113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034121 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 7]
def baseStart_1034121 : Nat := 118140960795 + 1034121 * 2 ^ 59
def prefixEnd_1034121 : Nat := 4983230072969 + 3 ^ 40 * 1034121 * 2
def baseEnd_1034121 : Nat := 236000501292557213569631

theorem tailTrace_1034121 : CollatzResearch.WordTrace tailWord_1034121 prefixEnd_1034121 236000501292557213569631 := by
  unfold tailWord_1034121
  simp only [CollatzResearch.WordTrace]
  refine ⟨37717491486563705650966217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25144994324375803767310811 37717491486563705650966217)
  ·
    refine ⟨28288118614922779238224663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37717491486563705650966217 28288118614922779238224663)
    ·
      refine ⟨42432177922384168857336995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28288118614922779238224663 42432177922384168857336995)
      ·
        refine ⟨63648266883576253286005493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42432177922384168857336995 63648266883576253286005493)
        ·
          refine ⟨5967025020335273745563015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63648266883576253286005493 5967025020335273745563015)
          ·
            refine ⟨8950537530502910618344523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5967025020335273745563015 8950537530502910618344523)
            ·
              refine ⟨13425806295754365927516785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8950537530502910618344523 13425806295754365927516785)
              ·
                refine ⟨10069354721815774445637589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13425806295754365927516785 10069354721815774445637589)
                ·
                  refine ⟨236000501292557213569631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10069354721815774445637589 236000501292557213569631)
                  ·
                    rfl

theorem cell21_1034121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_1034121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1034121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1034121 prefixEnd_1034121 := by exact prefixLift 1034121
  have htrace : WordTrace (prefixWord ++ tailWord_1034121) baseStart_1034121 baseEnd_1034121 := by
    simpa [prefixWord, tailWord_1034121, baseEnd_1034121] using wordTrace_append hprefix tailTrace_1034121
  have hstable : (prefixWord ++ tailWord_1034121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034121).length < 2 ^ (prefixWord ++ tailWord_1034121).sum := by decide
  have hdescent : baseEnd_1034121 < baseStart_1034121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034138 : List Nat := [3, 1, 1, 4, 2, 1, 1, 3, 5]
def baseStart_1034138 : Nat := 118140960795 + 1034138 * 2 ^ 59
def prefixEnd_1034138 : Nat := 4983230072969 + 3 ^ 40 * 1034138 * 2
def baseEnd_1034138 : Nat := 236004380924168961786263

theorem tailTrace_1034138 : CollatzResearch.WordTrace tailWord_1034138 prefixEnd_1034138 236004380924168961786263 := by
  unfold tailWord_1034138
  simp only [CollatzResearch.WordTrace]
  refine ⟨9429527881875529388583767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25145407685001411702890045 9429527881875529388583767)
  ·
    refine ⟨14144291822813294082875651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9429527881875529388583767 14144291822813294082875651)
    ·
      refine ⟨21216437734219941124313477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14144291822813294082875651 21216437734219941124313477)
      ·
        refine ⟨3978082075166238960808777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21216437734219941124313477 3978082075166238960808777)
        ·
          refine ⟨2983561556374679220606583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3978082075166238960808777 2983561556374679220606583)
          ·
            refine ⟨4475342334562018830909875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2983561556374679220606583 4475342334562018830909875)
            ·
              refine ⟨6713013501843028246364813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4475342334562018830909875 6713013501843028246364813)
              ·
                refine ⟨2517380063191135592386805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6713013501843028246364813 2517380063191135592386805)
                ·
                  refine ⟨236004380924168961786263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2517380063191135592386805 236004380924168961786263)
                  ·
                    rfl

theorem cell21_1034138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_1034138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1034138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1034138 prefixEnd_1034138 := by exact prefixLift 1034138
  have htrace : WordTrace (prefixWord ++ tailWord_1034138) baseStart_1034138 baseEnd_1034138 := by
    simpa [prefixWord, tailWord_1034138, baseEnd_1034138] using wordTrace_append hprefix tailTrace_1034138
  have hstable : (prefixWord ++ tailWord_1034138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034138).length < 2 ^ (prefixWord ++ tailWord_1034138).sum := by decide
  have hdescent : baseEnd_1034138 < baseStart_1034138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034158 : List Nat := [4, 1, 5, 1, 1, 1, 1, 7]
def baseStart_1034158 : Nat := 118140960795 + 1034158 * 2 ^ 59
def prefixEnd_1034158 : Nat := 4983230072969 + 3 ^ 40 * 1034158 * 2
def baseEnd_1034158 : Nat := 78669648398884457150963

theorem tailTrace_1034158 : CollatzResearch.WordTrace tailWord_1034158 prefixEnd_1034158 78669648398884457150963 := by
  unfold tailWord_1034158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4714855123428707621257891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25145893991619773980042085 4714855123428707621257891)
  ·
    refine ⟨7072282685143061431886837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4714855123428707621257891 7072282685143061431886837)
    ·
      refine ⟨663026501732162009239391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7072282685143061431886837 663026501732162009239391)
      ·
        refine ⟨994539752598243013859087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663026501732162009239391 994539752598243013859087)
        ·
          refine ⟨1491809628897364520788631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994539752598243013859087 1491809628897364520788631)
          ·
            refine ⟨2237714443346046781182947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491809628897364520788631 2237714443346046781182947)
            ·
              refine ⟨3356571665019070171774421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2237714443346046781182947 3356571665019070171774421)
              ·
                refine ⟨78669648398884457150963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3356571665019070171774421 78669648398884457150963)
                ·
                  rfl

theorem cell21_1034158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_1034158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1034158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1034158 prefixEnd_1034158 := by exact prefixLift 1034158
  have htrace : WordTrace (prefixWord ++ tailWord_1034158) baseStart_1034158 baseEnd_1034158 := by
    simpa [prefixWord, tailWord_1034158, baseEnd_1034158] using wordTrace_append hprefix tailTrace_1034158
  have hstable : (prefixWord ++ tailWord_1034158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034158).length < 2 ^ (prefixWord ++ tailWord_1034158).sum := by decide
  have hdescent : baseEnd_1034158 < baseStart_1034158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034245 : List Nat := [1, 3, 1, 1, 2, 5, 2, 2, 4]
def baseStart_1034245 : Nat := 118140960795 + 1034245 * 2 ^ 59
def prefixEnd_1034245 : Nat := 4983230072969 + 3 ^ 40 * 1034245 * 2
def baseEnd_1034245 : Nat := 236028799781960553502711

theorem tailTrace_1034245 : CollatzResearch.WordTrace tailWord_1034245 prefixEnd_1034245 236028799781960553502711 := by
  unfold tailWord_1034245
  simp only [CollatzResearch.WordTrace]
  refine ⟨37722014138114474828480189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25148009425409649885653459 37722014138114474828480189)
  ·
    refine ⟨14145755301792928060680071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37722014138114474828480189 14145755301792928060680071)
    ·
      refine ⟨21218632952689392091020107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14145755301792928060680071 21218632952689392091020107)
      ·
        refine ⟨31827949429034088136530161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21218632952689392091020107 31827949429034088136530161)
        ·
          refine ⟨23870962071775566102397621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31827949429034088136530161 23870962071775566102397621)
          ·
            refine ⟨2237902694228959322099777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23870962071775566102397621 2237902694228959322099777)
            ·
              refine ⟨1678427020671719491574833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2237902694228959322099777 1678427020671719491574833)
              ·
                refine ⟨1258820265503789618681125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1678427020671719491574833 1258820265503789618681125)
                ·
                  refine ⟨236028799781960553502711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1258820265503789618681125 236028799781960553502711)
                  ·
                    rfl

theorem cell21_1034245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_1034245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1034245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1034245 prefixEnd_1034245 := by exact prefixLift 1034245
  have htrace : WordTrace (prefixWord ++ tailWord_1034245) baseStart_1034245 baseEnd_1034245 := by
    simpa [prefixWord, tailWord_1034245, baseEnd_1034245] using wordTrace_append hprefix tailTrace_1034245
  have hstable : (prefixWord ++ tailWord_1034245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034245).length < 2 ^ (prefixWord ++ tailWord_1034245).sum := by decide
  have hdescent : baseEnd_1034245 < baseStart_1034245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034304 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 6]
def baseStart_1034304 : Nat := 118140960795 + 1034304 * 2 ^ 59
def prefixEnd_1034304 : Nat := 4983230072969 + 3 ^ 40 * 1034304 * 2
def baseEnd_1034304 : Nat := 236042264385789562019257

theorem tailTrace_1034304 : CollatzResearch.WordTrace tailWord_1034304 prefixEnd_1034304 236042264385789562019257 := by
  unfold tailWord_1034304
  simp only [CollatzResearch.WordTrace]
  refine ⟨18862083022450363952438983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25149444029933818603251977 18862083022450363952438983)
  ·
    refine ⟨28293124533675545928658475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18862083022450363952438983 28293124533675545928658475)
    ·
      refine ⟨42439686800513318892987713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28293124533675545928658475 42439686800513318892987713)
      ·
        refine ⟨31829765100384989169740785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42439686800513318892987713 31829765100384989169740785)
        ·
          refine ⟨23872323825288741877305589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31829765100384989169740785 23872323825288741877305589)
          ·
            refine ⟨2238030358620819550997399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23872323825288741877305589 2238030358620819550997399)
            ·
              refine ⟨3357045537931229326496099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2238030358620819550997399 3357045537931229326496099)
              ·
                refine ⟨5035568306896843989744149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357045537931229326496099 5035568306896843989744149)
                ·
                  refine ⟨236042264385789562019257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5035568306896843989744149 236042264385789562019257)
                  ·
                    rfl

theorem cell21_1034304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_1034304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1034304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1034304 prefixEnd_1034304 := by exact prefixLift 1034304
  have htrace : WordTrace (prefixWord ++ tailWord_1034304) baseStart_1034304 baseEnd_1034304 := by
    simpa [prefixWord, tailWord_1034304, baseEnd_1034304] using wordTrace_append hprefix tailTrace_1034304
  have hstable : (prefixWord ++ tailWord_1034304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034304).length < 2 ^ (prefixWord ++ tailWord_1034304).sum := by decide
  have hdescent : baseEnd_1034304 < baseStart_1034304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034417 : List Nat := [1, 2, 2, 5, 2, 2, 2, 2, 3]
def baseStart_1034417 : Nat := 118140960795 + 1034417 * 2 ^ 59
def prefixEnd_1034417 : Nat := 4983230072969 + 3 ^ 40 * 1034417 * 2
def baseEnd_1034417 : Nat := 236068052525326476635693

theorem tailTrace_1034417 : CollatzResearch.WordTrace tailWord_1034417 prefixEnd_1034417 236068052525326476635693 := by
  unfold tailWord_1034417
  simp only [CollatzResearch.WordTrace]
  refine ⟨37728287493491348203741505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25152191662327565469161003 37728287493491348203741505)
  ·
    refine ⟨28296215620118511152806129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37728287493491348203741505 28296215620118511152806129)
    ·
      refine ⟨21222161715088883364604597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28296215620118511152806129 21222161715088883364604597)
      ·
        refine ⟨1989577660789582815431681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21222161715088883364604597 1989577660789582815431681)
        ·
          refine ⟨1492183245592187111573761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1989577660789582815431681 1492183245592187111573761)
          ·
            refine ⟨1119137434194140333680321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1492183245592187111573761 1119137434194140333680321)
            ·
              refine ⟨839353075645605250260241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1119137434194140333680321 839353075645605250260241)
              ·
                refine ⟨629514806734203937695181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839353075645605250260241 629514806734203937695181)
                ·
                  refine ⟨236068052525326476635693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 629514806734203937695181 236068052525326476635693)
                  ·
                    rfl

theorem cell21_1034417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 3].length) (baseStart_1034417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1034417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1034417 prefixEnd_1034417 := by exact prefixLift 1034417
  have htrace : WordTrace (prefixWord ++ tailWord_1034417) baseStart_1034417 baseEnd_1034417 := by
    simpa [prefixWord, tailWord_1034417, baseEnd_1034417] using wordTrace_append hprefix tailTrace_1034417
  have hstable : (prefixWord ++ tailWord_1034417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034417).length < 2 ^ (prefixWord ++ tailWord_1034417).sum := by decide
  have hdescent : baseEnd_1034417 < baseStart_1034417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034425 : List Nat := [1, 2, 1, 4, 1, 2, 2, 3, 5]
def baseStart_1034425 : Nat := 118140960795 + 1034425 * 2 ^ 59
def prefixEnd_1034425 : Nat := 4983230072969 + 3 ^ 40 * 1034425 * 2
def baseEnd_1034425 : Nat := 236069878234320240502343

theorem tailTrace_1034425 : CollatzResearch.WordTrace tailWord_1034425 prefixEnd_1034425 236069878234320240502343 := by
  unfold tailWord_1034425
  simp only [CollatzResearch.WordTrace]
  refine ⟨37728579277462365570032729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25152386184974910380021819 37728579277462365570032729)
  ·
    refine ⟨28296434458096774177524547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37728579277462365570032729 28296434458096774177524547)
    ·
      refine ⟨42444651687145161266286821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28296434458096774177524547 42444651687145161266286821)
      ·
        refine ⟨7958372191339717737428779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42444651687145161266286821 7958372191339717737428779)
        ·
          refine ⟨11937558287009576606143169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7958372191339717737428779 11937558287009576606143169)
          ·
            refine ⟨8953168715257182454607377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11937558287009576606143169 8953168715257182454607377)
            ·
              refine ⟨6714876536442886840955533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8953168715257182454607377 6714876536442886840955533)
              ·
                refine ⟨2518078701166082565358325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6714876536442886840955533 2518078701166082565358325)
                ·
                  refine ⟨236069878234320240502343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2518078701166082565358325 236069878234320240502343)
                  ·
                    rfl

theorem cell21_1034425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_1034425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1034425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1034425 prefixEnd_1034425 := by exact prefixLift 1034425
  have htrace : WordTrace (prefixWord ++ tailWord_1034425) baseStart_1034425 baseEnd_1034425 := by
    simpa [prefixWord, tailWord_1034425, baseEnd_1034425] using wordTrace_append hprefix tailTrace_1034425
  have hstable : (prefixWord ++ tailWord_1034425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034425).length < 2 ^ (prefixWord ++ tailWord_1034425).sum := by decide
  have hdescent : baseEnd_1034425 < baseStart_1034425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034428 : List Nat := [2, 2, 2, 3, 3, 2, 1, 6]
def baseStart_1034428 : Nat := 118140960795 + 1034428 * 2 ^ 59
def prefixEnd_1034428 : Nat := 4983230072969 + 3 ^ 40 * 1034428 * 2
def baseEnd_1034428 : Nat := 78690187625064300650779

theorem tailTrace_1034428 : CollatzResearch.WordTrace tailWord_1034428 prefixEnd_1034428 78690187625064300650779 := by
  unfold tailWord_1034428
  simp only [CollatzResearch.WordTrace]
  refine ⟨18864344348225748541195969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25152459130967664721594625 18864344348225748541195969)
  ·
    refine ⟨14148258261169311405896977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18864344348225748541195969 14148258261169311405896977)
    ·
      refine ⟨10611193695876983554422733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14148258261169311405896977 10611193695876983554422733)
      ·
        refine ⟨3979197635953868832908525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10611193695876983554422733 3979197635953868832908525)
        ·
          refine ⟨1492199113482700812340697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3979197635953868832908525 1492199113482700812340697)
          ·
            refine ⟨1119149335112025609255523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1492199113482700812340697 1119149335112025609255523)
            ·
              refine ⟨1678724002668038413883285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1119149335112025609255523 1678724002668038413883285)
              ·
                refine ⟨78690187625064300650779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1678724002668038413883285 78690187625064300650779)
                ·
                  rfl

theorem cell21_1034428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 6].length) (baseStart_1034428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1034428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1034428 prefixEnd_1034428 := by exact prefixLift 1034428
  have htrace : WordTrace (prefixWord ++ tailWord_1034428) baseStart_1034428 baseEnd_1034428 := by
    simpa [prefixWord, tailWord_1034428, baseEnd_1034428] using wordTrace_append hprefix tailTrace_1034428
  have hstable : (prefixWord ++ tailWord_1034428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034428).length < 2 ^ (prefixWord ++ tailWord_1034428).sum := by decide
  have hdescent : baseEnd_1034428 < baseStart_1034428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034439 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 10]
def baseStart_1034439 : Nat := 118140960795 + 1034439 * 2 ^ 59
def prefixEnd_1034439 : Nat := 4983230072969 + 3 ^ 40 * 1034439 * 2
def baseEnd_1034439 : Nat := 236073073225059327268981

theorem tailTrace_1034439 : CollatzResearch.WordTrace tailWord_1034439 prefixEnd_1034439 236073073225059327268981 := by
  unfold tailWord_1034439
  simp only [CollatzResearch.WordTrace]
  refine ⟨37729089899411645961042371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25152726599607763974028247 37729089899411645961042371)
  ·
    refine ⟨56593634849117468941563557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37729089899411645961042371 56593634849117468941563557)
    ·
      refine ⟨10611306534209525426543167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56593634849117468941563557 10611306534209525426543167)
      ·
        refine ⟨15916959801314288139814751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10611306534209525426543167 15916959801314288139814751)
        ·
          refine ⟨23875439701971432209722127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15916959801314288139814751 23875439701971432209722127)
          ·
            refine ⟨35813159552957148314583191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23875439701971432209722127 35813159552957148314583191)
            ·
              refine ⟨53719739329435722471874787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35813159552957148314583191 53719739329435722471874787)
              ·
                refine ⟨80579608994153583707812181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53719739329435722471874787 80579608994153583707812181)
                ·
                  refine ⟨236073073225059327268981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 80579608994153583707812181 236073073225059327268981)
                  ·
                    rfl

theorem cell21_1034439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 10].length) (baseStart_1034439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1034439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1034439 prefixEnd_1034439 := by exact prefixLift 1034439
  have htrace : WordTrace (prefixWord ++ tailWord_1034439) baseStart_1034439 baseEnd_1034439 := by
    simpa [prefixWord, tailWord_1034439, baseEnd_1034439] using wordTrace_append hprefix tailTrace_1034439
  have hstable : (prefixWord ++ tailWord_1034439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034439).length < 2 ^ (prefixWord ++ tailWord_1034439).sum := by decide
  have hdescent : baseEnd_1034439 < baseStart_1034439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034504 : List Nat := [2, 1, 3, 2, 3, 3, 2, 5]
def baseStart_1034504 : Nat := 118140960795 + 1034504 * 2 ^ 59
def prefixEnd_1034504 : Nat := 4983230072969 + 3 ^ 40 * 1034504 * 2
def baseEnd_1034504 : Nat := 78695969036877886228505

theorem tailTrace_1034504 : CollatzResearch.WordTrace tailWord_1034504 prefixEnd_1034504 78695969036877886228505 := by
  unfold tailWord_1034504
  simp only [CollatzResearch.WordTrace]
  refine ⟨18865730322088081031079283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25154307096117441374772377 18865730322088081031079283)
  ·
    refine ⟨28298595483132121546618925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18865730322088081031079283 28298595483132121546618925)
    ·
      refine ⟨10611973306174545579982097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28298595483132121546618925 10611973306174545579982097)
      ·
        refine ⟨7958979979630909184986573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10611973306174545579982097 7958979979630909184986573)
        ·
          refine ⟨2984617492361590944369965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7958979979630909184986573 2984617492361590944369965)
          ·
            refine ⟨1119231559635596604138737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2984617492361590944369965 1119231559635596604138737)
            ·
              refine ⟨839423669726697453104053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1119231559635596604138737 839423669726697453104053)
              ·
                refine ⟨78695969036877886228505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 839423669726697453104053 78695969036877886228505)
                ·
                  rfl

theorem cell21_1034504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 5].length) (baseStart_1034504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1034504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1034504 prefixEnd_1034504 := by exact prefixLift 1034504
  have htrace : WordTrace (prefixWord ++ tailWord_1034504) baseStart_1034504 baseEnd_1034504 := by
    simpa [prefixWord, tailWord_1034504, baseEnd_1034504] using wordTrace_append hprefix tailTrace_1034504
  have hstable : (prefixWord ++ tailWord_1034504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034504).length < 2 ^ (prefixWord ++ tailWord_1034504).sum := by decide
  have hdescent : baseEnd_1034504 < baseStart_1034504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034532 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 6]
def baseStart_1034532 : Nat := 118140960795 + 1034532 * 2 ^ 59
def prefixEnd_1034532 : Nat := 4983230072969 + 3 ^ 40 * 1034532 * 2
def baseEnd_1034532 : Nat := 236094297092111832218791

theorem tailTrace_1034532 : CollatzResearch.WordTrace tailWord_1034532 prefixEnd_1034532 236094297092111832218791 := by
  unfold tailWord_1034532
  simp only [CollatzResearch.WordTrace]
  refine ⟨18866240944037361422088925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25154987925383148562785233 18866240944037361422088925)
  ·
    refine ⟨7074840354014010533283347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18866240944037361422088925 7074840354014010533283347)
    ·
      refine ⟨10612260531021015799925021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7074840354014010533283347 10612260531021015799925021)
      ·
        refine ⟨3979597699132880924971883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10612260531021015799925021 3979597699132880924971883)
        ·
          refine ⟨5969396548699321387457825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3979597699132880924971883 5969396548699321387457825)
          ·
            refine ⟨4477047411524491040593369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5969396548699321387457825 4477047411524491040593369)
            ·
              refine ⟨3357785558643368280445027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4477047411524491040593369 3357785558643368280445027)
              ·
                refine ⟨5036678337965052420667541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357785558643368280445027 5036678337965052420667541)
                ·
                  refine ⟨236094297092111832218791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5036678337965052420667541 236094297092111832218791)
                  ·
                    rfl

theorem cell21_1034532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_1034532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1034532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1034532 prefixEnd_1034532 := by exact prefixLift 1034532
  have htrace : WordTrace (prefixWord ++ tailWord_1034532) baseStart_1034532 baseEnd_1034532 := by
    simpa [prefixWord, tailWord_1034532, baseEnd_1034532] using wordTrace_append hprefix tailTrace_1034532
  have hstable : (prefixWord ++ tailWord_1034532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034532).length < 2 ^ (prefixWord ++ tailWord_1034532).sum := by decide
  have hdescent : baseEnd_1034532 < baseStart_1034532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034591 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 6]
def baseStart_1034591 : Nat := 118140960795 + 1034591 * 2 ^ 59
def prefixEnd_1034591 : Nat := 4983230072969 + 3 ^ 40 * 1034591 * 2
def baseEnd_1034591 : Nat := 236107761695940840735337

theorem tailTrace_1034591 : CollatzResearch.WordTrace tailWord_1034591 prefixEnd_1034591 236107761695940840735337 := by
  unfold tailWord_1034591
  simp only [CollatzResearch.WordTrace]
  refine ⟨37734633794860975920575627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25156422529907317280383751 37734633794860975920575627)
  ·
    refine ⟨56601950692291463880863441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37734633794860975920575627 56601950692291463880863441)
    ·
      refine ⟨42451463019218597910647581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56601950692291463880863441 42451463019218597910647581)
      ·
        refine ⟨15919298632206974216492843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42451463019218597910647581 15919298632206974216492843)
        ·
          refine ⟨23878947948310461324739265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15919298632206974216492843 23878947948310461324739265)
          ·
            refine ⟨17909210961232845993554449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23878947948310461324739265 17909210961232845993554449)
            ·
              refine ⟨13431908220924634495165837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17909210961232845993554449 13431908220924634495165837)
              ·
                refine ⟨5036965582846737935687189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13431908220924634495165837 5036965582846737935687189)
                ·
                  refine ⟨236107761695940840735337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5036965582846737935687189 236107761695940840735337)
                  ·
                    rfl

theorem cell21_1034591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 6].length) (baseStart_1034591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1034591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1034591 prefixEnd_1034591 := by exact prefixLift 1034591
  have htrace : WordTrace (prefixWord ++ tailWord_1034591) baseStart_1034591 baseEnd_1034591 := by
    simpa [prefixWord, tailWord_1034591, baseEnd_1034591] using wordTrace_append hprefix tailTrace_1034591
  have hstable : (prefixWord ++ tailWord_1034591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034591).length < 2 ^ (prefixWord ++ tailWord_1034591).sum := by decide
  have hdescent : baseEnd_1034591 < baseStart_1034591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034608 : List Nat := [2, 1, 1, 1, 4, 3, 2, 3, 4]
def baseStart_1034608 : Nat := 118140960795 + 1034608 * 2 ^ 59
def prefixEnd_1034608 : Nat := 4983230072969 + 3 ^ 40 * 1034608 * 2
def baseEnd_1034608 : Nat := 236111641327552588951969

theorem tailTrace_1034608 : CollatzResearch.WordTrace tailWord_1034608 prefixEnd_1034608 236111641327552588951969 := by
  unfold tailWord_1034608
  simp only [CollatzResearch.WordTrace]
  refine ⟨18867626917899693911972239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25156835890532925215962985 18867626917899693911972239)
  ·
    refine ⟨28301440376849540867958359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18867626917899693911972239 28301440376849540867958359)
    ·
      refine ⟨42452160565274311301937539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28301440376849540867958359 42452160565274311301937539)
      ·
        refine ⟨63678240847911466952906309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42452160565274311301937539 63678240847911466952906309)
        ·
          refine ⟨11939670158983400053669933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63678240847911466952906309 11939670158983400053669933)
          ·
            refine ⟨4477376309618775020126225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11939670158983400053669933 4477376309618775020126225)
            ·
              refine ⟨3358032232214081265094669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4477376309618775020126225 3358032232214081265094669)
              ·
                refine ⟨1259262087080280474410501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3358032232214081265094669 1259262087080280474410501)
                ·
                  refine ⟨236111641327552588951969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1259262087080280474410501 236111641327552588951969)
                  ·
                    rfl

theorem cell21_1034608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 4].length) (baseStart_1034608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1034608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1034608 prefixEnd_1034608 := by exact prefixLift 1034608
  have htrace : WordTrace (prefixWord ++ tailWord_1034608) baseStart_1034608 baseEnd_1034608 := by
    simpa [prefixWord, tailWord_1034608, baseEnd_1034608] using wordTrace_append hprefix tailTrace_1034608
  have hstable : (prefixWord ++ tailWord_1034608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034608).length < 2 ^ (prefixWord ++ tailWord_1034608).sum := by decide
  have hdescent : baseEnd_1034608 < baseStart_1034608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034684 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 6]
def baseStart_1034684 : Nat := 118140960795 + 1034684 * 2 ^ 59
def prefixEnd_1034684 : Nat := 4983230072969 + 3 ^ 40 * 1034684 * 2
def baseEnd_1034684 : Nat := 236128985562993345685147

theorem tailTrace_1034684 : CollatzResearch.WordTrace tailWord_1034684 prefixEnd_1034684 236128985562993345685147 := by
  unfold tailWord_1034684
  simp only [CollatzResearch.WordTrace]
  refine ⟨18869012891762026401855553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25158683855682701869140737 18869012891762026401855553)
  ·
    refine ⟨14151759668821519801391665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18869012891762026401855553 14151759668821519801391665)
    ·
      refine ⟨10613819751616139851043749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14151759668821519801391665 10613819751616139851043749)
      ·
        refine ⟨1990091203428026222070703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10613819751616139851043749 1990091203428026222070703)
        ·
          refine ⟨2985136805142039333106055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1990091203428026222070703 2985136805142039333106055)
          ·
            refine ⟨4477705207713058999659083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2985136805142039333106055 4477705207713058999659083)
            ·
              refine ⟨6716557811569588499488625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4477705207713058999659083 6716557811569588499488625)
              ·
                refine ⟨5037418358677191374616469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6716557811569588499488625 5037418358677191374616469)
                ·
                  refine ⟨236128985562993345685147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5037418358677191374616469 236128985562993345685147)
                  ·
                    rfl

theorem cell21_1034684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_1034684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1034684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1034684 prefixEnd_1034684 := by exact prefixLift 1034684
  have htrace : WordTrace (prefixWord ++ tailWord_1034684) baseStart_1034684 baseEnd_1034684 := by
    simpa [prefixWord, tailWord_1034684, baseEnd_1034684] using wordTrace_append hprefix tailTrace_1034684
  have hstable : (prefixWord ++ tailWord_1034684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034684).length < 2 ^ (prefixWord ++ tailWord_1034684).sum := by decide
  have hdescent : baseEnd_1034684 < baseStart_1034684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034763 : List Nat := [1, 1, 1, 1, 7, 1, 4, 2, 3]
def baseStart_1034763 : Nat := 118140960795 + 1034763 * 2 ^ 59
def prefixEnd_1034763 : Nat := 4983230072969 + 3 ^ 40 * 1034763 * 2
def baseEnd_1034763 : Nat := 236147014439306763868319

theorem tailTrace_1034763 : CollatzResearch.WordTrace tailWord_1034763 prefixEnd_1034763 236147014439306763868319 := by
  unfold tailWord_1034763
  simp only [CollatzResearch.WordTrace]
  refine ⟨37740907150237849295836943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25160604766825232863891295 37740907150237849295836943)
  ·
    refine ⟨56611360725356773943755415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37740907150237849295836943 56611360725356773943755415)
    ·
      refine ⟨84917041088035160915633123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56611360725356773943755415 84917041088035160915633123)
      ·
        refine ⟨127375561632052741373449685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84917041088035160915633123 127375561632052741373449685)
        ·
          refine ⟨2985364725751236125940227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 127375561632052741373449685 2985364725751236125940227)
          ·
            refine ⟨4478047088626854188910341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2985364725751236125940227 4478047088626854188910341)
            ·
              refine ⟨839633829117535160420689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4478047088626854188910341 839633829117535160420689)
              ·
                refine ⟨629725371838151370315517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839633829117535160420689 629725371838151370315517)
                ·
                  refine ⟨236147014439306763868319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 629725371838151370315517 236147014439306763868319)
                  ·
                    rfl

theorem cell21_1034763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 3].length) (baseStart_1034763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1034763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1034763 prefixEnd_1034763 := by exact prefixLift 1034763
  have htrace : WordTrace (prefixWord ++ tailWord_1034763) baseStart_1034763 baseEnd_1034763 := by
    simpa [prefixWord, tailWord_1034763, baseEnd_1034763] using wordTrace_append hprefix tailTrace_1034763
  have hstable : (prefixWord ++ tailWord_1034763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034763).length < 2 ^ (prefixWord ++ tailWord_1034763).sum := by decide
  have hdescent : baseEnd_1034763 < baseStart_1034763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034856 : List Nat := [2, 1, 4, 3, 2, 2, 1, 3, 3]
def baseStart_1034856 : Nat := 118140960795 + 1034856 * 2 ^ 59
def prefixEnd_1034856 : Nat := 4983230072969 + 3 ^ 40 * 1034856 * 2
def baseEnd_1034856 : Nat := 236168238306359268818129

theorem tailTrace_1034856 : CollatzResearch.WordTrace tailWord_1034856 prefixEnd_1034856 236168238306359268818129 := by
  unfold tailWord_1034856
  simp only [CollatzResearch.WordTrace]
  refine ⟨18872149569450463089486211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25162866092600617452648281 18872149569450463089486211)
  ·
    refine ⟨28308224354175694634229317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18872149569450463089486211 28308224354175694634229317)
    ·
      refine ⟨5307792066407942743917997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28308224354175694634229317 5307792066407942743917997)
      ·
        refine ⟨1990422024902978528969249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5307792066407942743917997 1990422024902978528969249)
        ·
          refine ⟨1492816518677233896726937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1990422024902978528969249 1492816518677233896726937)
          ·
            refine ⟨1119612389007925422545203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1492816518677233896726937 1119612389007925422545203)
            ·
              refine ⟨1679418583511888133817805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1119612389007925422545203 1679418583511888133817805)
              ·
                refine ⟨629781968816958050181677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1679418583511888133817805 629781968816958050181677)
                ·
                  refine ⟨236168238306359268818129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 629781968816958050181677 236168238306359268818129)
                  ·
                    rfl

theorem cell21_1034856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 3].length) (baseStart_1034856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1034856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1034856 prefixEnd_1034856 := by exact prefixLift 1034856
  have htrace : WordTrace (prefixWord ++ tailWord_1034856) baseStart_1034856 baseEnd_1034856 := by
    simpa [prefixWord, tailWord_1034856, baseEnd_1034856] using wordTrace_append hprefix tailTrace_1034856
  have hstable : (prefixWord ++ tailWord_1034856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034856).length < 2 ^ (prefixWord ++ tailWord_1034856).sum := by decide
  have hdescent : baseEnd_1034856 < baseStart_1034856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034895 : List Nat := [1, 1, 2, 1, 1, 1, 1, 9, 4]
def baseStart_1034895 : Nat := 118140960795 + 1034895 * 2 ^ 59
def prefixEnd_1034895 : Nat := 4983230072969 + 3 ^ 40 * 1034895 * 2
def baseEnd_1034895 : Nat := 236177138637703867668049

theorem tailTrace_1034895 : CollatzResearch.WordTrace tailWord_1034895 prefixEnd_1034895 236177138637703867668049 := by
  unfold tailWord_1034895
  simp only [CollatzResearch.WordTrace]
  refine ⟨37745721585759635839642139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25163814390506423893094759 37745721585759635839642139)
  ·
    refine ⟨56618582378639453759463209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37745721585759635839642139 56618582378639453759463209)
    ·
      refine ⟨42463936783979590319597407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56618582378639453759463209 42463936783979590319597407)
      ·
        refine ⟨63695905175969385479396111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42463936783979590319597407 63695905175969385479396111)
        ·
          refine ⟨95543857763954078219094167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63695905175969385479396111 95543857763954078219094167)
          ·
            refine ⟨143315786645931117328641251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95543857763954078219094167 143315786645931117328641251)
            ·
              refine ⟨214973679968896675992961877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143315786645931117328641251 214973679968896675992961877)
              ·
                refine ⟨1259611406067753960896261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 214973679968896675992961877 1259611406067753960896261)
                ·
                  refine ⟨236177138637703867668049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1259611406067753960896261 236177138637703867668049)
                  ·
                    rfl

theorem cell21_1034895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 4].length) (baseStart_1034895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1034895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1034895 prefixEnd_1034895 := by exact prefixLift 1034895
  have htrace : WordTrace (prefixWord ++ tailWord_1034895) baseStart_1034895 baseEnd_1034895 := by
    simpa [prefixWord, tailWord_1034895, baseEnd_1034895] using wordTrace_append hprefix tailTrace_1034895
  have hstable : (prefixWord ++ tailWord_1034895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034895).length < 2 ^ (prefixWord ++ tailWord_1034895).sum := by decide
  have hdescent : baseEnd_1034895 < baseStart_1034895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035033 : List Nat := [1, 2, 1, 2, 1, 1, 1, 9, 3]
def baseStart_1035033 : Nat := 118140960795 + 1035033 * 2 ^ 59
def prefixEnd_1035033 : Nat := 4983230072969 + 3 ^ 40 * 1035033 * 2
def baseEnd_1035033 : Nat := 236208632117846294367767

theorem tailTrace_1035033 : CollatzResearch.WordTrace tailWord_1035033 prefixEnd_1035033 236208632117846294367767 := by
  unfold tailWord_1035033
  simp only [CollatzResearch.WordTrace]
  refine ⟨37750754859259685408165753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25167169906173123605443835 37750754859259685408165753)
  ·
    refine ⟨28313066144444764056124315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37750754859259685408165753 28313066144444764056124315)
    ·
      refine ⟨42469599216667146084186473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28313066144444764056124315 42469599216667146084186473)
      ·
        refine ⟨31852199412500359563139855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42469599216667146084186473 31852199412500359563139855)
        ·
          refine ⟨47778299118750539344709783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31852199412500359563139855 47778299118750539344709783)
          ·
            refine ⟨71667448678125809017064675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47778299118750539344709783 71667448678125809017064675)
            ·
              refine ⟨107501173017188713525597013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71667448678125809017064675 107501173017188713525597013)
              ·
                refine ⟨629889685647590118314045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 107501173017188713525597013 629889685647590118314045)
                ·
                  refine ⟨236208632117846294367767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 629889685647590118314045 236208632117846294367767)
                  ·
                    rfl

theorem cell21_1035033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 3].length) (baseStart_1035033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035033 prefixEnd_1035033 := by exact prefixLift 1035033
  have htrace : WordTrace (prefixWord ++ tailWord_1035033) baseStart_1035033 baseEnd_1035033 := by
    simpa [prefixWord, tailWord_1035033, baseEnd_1035033] using wordTrace_append hprefix tailTrace_1035033
  have hstable : (prefixWord ++ tailWord_1035033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035033).length < 2 ^ (prefixWord ++ tailWord_1035033).sum := by decide
  have hdescent : baseEnd_1035033 < baseStart_1035033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035123 : List Nat := [1, 1, 1, 2, 2, 1, 6, 3, 4]
def baseStart_1035123 : Nat := 118140960795 + 1035123 * 2 ^ 59
def prefixEnd_1035123 : Nat := 4983230072969 + 3 ^ 40 * 1035123 * 2
def baseEnd_1035123 : Nat := 236229171344026137867583

theorem tailTrace_1035123 : CollatzResearch.WordTrace tailWord_1035123 prefixEnd_1035123 236229171344026137867583 := by
  unfold tailWord_1035123
  simp only [CollatzResearch.WordTrace]
  refine ⟨37754037428933630778942023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25169358285955753852628015 37754037428933630778942023)
  ·
    refine ⟨56631056143400446168413035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37754037428933630778942023 56631056143400446168413035)
    ·
      refine ⟨84946584215100669252619553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56631056143400446168413035 84946584215100669252619553)
      ·
        refine ⟨63709938161325501939464665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84946584215100669252619553 63709938161325501939464665)
        ·
          refine ⟨47782453620994126454598499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63709938161325501939464665 47782453620994126454598499)
          ·
            refine ⟨71673680431491189681897749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47782453620994126454598499 71673680431491189681897749)
            ·
              refine ⟨3359703770226149516338957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71673680431491189681897749 3359703770226149516338957)
              ·
                refine ⟨1259888913834806068627109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3359703770226149516338957 1259888913834806068627109)
                ·
                  refine ⟨236229171344026137867583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1259888913834806068627109 236229171344026137867583)
                  ·
                    rfl

theorem cell21_1035123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 4].length) (baseStart_1035123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035123 prefixEnd_1035123 := by exact prefixLift 1035123
  have htrace : WordTrace (prefixWord ++ tailWord_1035123) baseStart_1035123 baseEnd_1035123 := by
    simpa [prefixWord, tailWord_1035123, baseEnd_1035123] using wordTrace_append hprefix tailTrace_1035123
  have hstable : (prefixWord ++ tailWord_1035123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035123).length < 2 ^ (prefixWord ++ tailWord_1035123).sum := by decide
  have hdescent : baseEnd_1035123 < baseStart_1035123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035126 : List Nat := [5, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_1035126 : Nat := 118140960795 + 1035126 * 2 ^ 59
def prefixEnd_1035126 : Nat := 4983230072969 + 3 ^ 40 * 1035126 * 2
def baseEnd_1035126 : Nat := 236229855984898799317577

theorem tailTrace_1035126 : CollatzResearch.WordTrace tailWord_1035126 prefixEnd_1035126 236229855984898799317577 := by
  unfold tailWord_1035126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2359634177995172643206327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25169431231948508194200821 2359634177995172643206327)
  ·
    refine ⟨3539451266992758964809491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2359634177995172643206327 3539451266992758964809491)
    ·
      refine ⟨5309176900489138447214237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3539451266992758964809491 5309176900489138447214237)
      ·
        refine ⟨1990941337683426917705339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5309176900489138447214237 1990941337683426917705339)
        ·
          refine ⟨2986412006525140376558009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1990941337683426917705339 2986412006525140376558009)
          ·
            refine ⟨2239809004893855282418507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2986412006525140376558009 2239809004893855282418507)
            ·
              refine ⟨3359713507340782923627761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239809004893855282418507 3359713507340782923627761)
              ·
                refine ⟨2519785130505587192720821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3359713507340782923627761 2519785130505587192720821)
                ·
                  refine ⟨236229855984898799317577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2519785130505587192720821 236229855984898799317577)
                  ·
                    rfl

theorem cell21_1035126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_1035126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035126 prefixEnd_1035126 := by exact prefixLift 1035126
  have htrace : WordTrace (prefixWord ++ tailWord_1035126) baseStart_1035126 baseEnd_1035126 := by
    simpa [prefixWord, tailWord_1035126, baseEnd_1035126] using wordTrace_append hprefix tailTrace_1035126
  have hstable : (prefixWord ++ tailWord_1035126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035126).length < 2 ^ (prefixWord ++ tailWord_1035126).sum := by decide
  have hdescent : baseEnd_1035126 < baseStart_1035126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035168 : List Nat := [2, 1, 1, 4, 1, 1, 3, 3, 5]
def baseStart_1035168 : Nat := 118140960795 + 1035168 * 2 ^ 59
def prefixEnd_1035168 : Nat := 4983230072969 + 3 ^ 40 * 1035168 * 2
def baseEnd_1035168 : Nat := 236239440957116059617491

theorem tailTrace_1035168 : CollatzResearch.WordTrace tailWord_1035168 prefixEnd_1035168 236239440957116059617491 := by
  unfold tailWord_1035168
  simp only [CollatzResearch.WordTrace]
  refine ⟨18877839356885301732165079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25170452475847068976220105 18877839356885301732165079)
  ·
    refine ⟨28316759035327952598247619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18877839356885301732165079 28316759035327952598247619)
    ·
      refine ⟨42475138552991928897371429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28316759035327952598247619 42475138552991928897371429)
      ·
        refine ⟨7964088478685986668257143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42475138552991928897371429 7964088478685986668257143)
        ·
          refine ⟨11946132718028980002385715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7964088478685986668257143 11946132718028980002385715)
          ·
            refine ⟨17919199077043470003578573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11946132718028980002385715 17919199077043470003578573)
            ·
              refine ⟨6719699653891301251341965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17919199077043470003578573 6719699653891301251341965)
              ·
                refine ⟨2519887370209237969253237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6719699653891301251341965 2519887370209237969253237)
                ·
                  refine ⟨236239440957116059617491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2519887370209237969253237 236239440957116059617491)
                  ·
                    rfl

theorem cell21_1035168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_1035168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035168 prefixEnd_1035168 := by exact prefixLift 1035168
  have htrace : WordTrace (prefixWord ++ tailWord_1035168) baseStart_1035168 baseEnd_1035168 := by
    simpa [prefixWord, tailWord_1035168, baseEnd_1035168] using wordTrace_append hprefix tailTrace_1035168
  have hstable : (prefixWord ++ tailWord_1035168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035168).length < 2 ^ (prefixWord ++ tailWord_1035168).sum := by decide
  have hdescent : baseEnd_1035168 < baseStart_1035168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035188 : List Nat := [2, 5, 2, 1, 1, 1, 4, 5]
def baseStart_1035188 : Nat := 118140960795 + 1035188 * 2 ^ 59
def prefixEnd_1035188 : Nat := 4983230072969 + 3 ^ 40 * 1035188 * 2
def baseEnd_1035188 : Nat := 78748001743200156428039

theorem tailTrace_1035188 : CollatzResearch.WordTrace tailWord_1035188 prefixEnd_1035188 78748001743200156428039 := by
  unfold tailWord_1035188
  simp only [CollatzResearch.WordTrace]
  refine ⟨18878204086849073440029109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25170938782465431253372145 18878204086849073440029109)
  ·
    refine ⟨1769831633142100635002729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18878204086849073440029109 1769831633142100635002729)
    ·
      refine ⟨1327373724856575476252047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1769831633142100635002729 1327373724856575476252047)
      ·
        refine ⟨1991060587284863214378071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1327373724856575476252047 1991060587284863214378071)
        ·
          refine ⟨2986590880927294821567107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991060587284863214378071 2986590880927294821567107)
          ·
            refine ⟨4479886321390942232350661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2986590880927294821567107 4479886321390942232350661)
            ·
              refine ⟨839978685260801668565749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4479886321390942232350661 839978685260801668565749)
              ·
                refine ⟨78748001743200156428039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 839978685260801668565749 78748001743200156428039)
                ·
                  rfl

theorem cell21_1035188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 5].length) (baseStart_1035188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035188 prefixEnd_1035188 := by exact prefixLift 1035188
  have htrace : WordTrace (prefixWord ++ tailWord_1035188) baseStart_1035188 baseEnd_1035188 := by
    simpa [prefixWord, tailWord_1035188, baseEnd_1035188] using wordTrace_append hprefix tailTrace_1035188
  have hstable : (prefixWord ++ tailWord_1035188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035188).length < 2 ^ (prefixWord ++ tailWord_1035188).sum := by decide
  have hdescent : baseEnd_1035188 < baseStart_1035188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035258 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 8]
def baseStart_1035258 : Nat := 118140960795 + 1035258 * 2 ^ 59
def prefixEnd_1035258 : Nat := 4983230072969 + 3 ^ 40 * 1035258 * 2
def baseEnd_1035258 : Nat := 236259980183295903117307

theorem tailTrace_1035258 : CollatzResearch.WordTrace tailWord_1035258 prefixEnd_1035258 236259980183295903117307 := by
  unfold tailWord_1035258
  simp only [CollatzResearch.WordTrace]
  refine ⟨9439740320861137208776607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25172640855629699223404285 9439740320861137208776607)
  ·
    refine ⟨14159610481291705813164911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9439740320861137208776607 14159610481291705813164911)
    ·
      refine ⟨21239415721937558719747367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14159610481291705813164911 21239415721937558719747367)
      ·
        refine ⟨31859123582906338079621051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21239415721937558719747367 31859123582906338079621051)
        ·
          refine ⟨47788685374359507119431577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31859123582906338079621051 47788685374359507119431577)
          ·
            refine ⟨35841514030769630339573683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47788685374359507119431577 35841514030769630339573683)
            ·
              refine ⟨53762271046154445509360525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35841514030769630339573683 53762271046154445509360525)
              ·
                refine ⟨20160851642307917066010197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53762271046154445509360525 20160851642307917066010197)
                ·
                  refine ⟨236259980183295903117307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20160851642307917066010197 236259980183295903117307)
                  ·
                    rfl

theorem cell21_1035258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_1035258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035258 prefixEnd_1035258 := by exact prefixLift 1035258
  have htrace : WordTrace (prefixWord ++ tailWord_1035258) baseStart_1035258 baseEnd_1035258 := by
    simpa [prefixWord, tailWord_1035258, baseEnd_1035258] using wordTrace_append hprefix tailTrace_1035258
  have hstable : (prefixWord ++ tailWord_1035258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035258).length < 2 ^ (prefixWord ++ tailWord_1035258).sum := by decide
  have hdescent : baseEnd_1035258 < baseStart_1035258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035261 : List Nat := [1, 4, 1, 1, 1, 2, 1, 7, 3]
def baseStart_1035261 : Nat := 118140960795 + 1035261 * 2 ^ 59
def prefixEnd_1035261 : Nat := 4983230072969 + 3 ^ 40 * 1035261 * 2
def baseEnd_1035261 : Nat := 236260664824168564567301

theorem tailTrace_1035261 : CollatzResearch.WordTrace tailWord_1035261 prefixEnd_1035261 236260664824168564567301 := by
  unfold tailWord_1035261
  simp only [CollatzResearch.WordTrace]
  refine ⟨37759070702433680347465637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25172713801622453564977091 37759070702433680347465637)
  ·
    refine ⟨7079825756706315065149807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37759070702433680347465637 7079825756706315065149807)
    ·
      refine ⟨10619738635059472597724711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7079825756706315065149807 10619738635059472597724711)
      ·
        refine ⟨15929607952589208896587067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10619738635059472597724711 15929607952589208896587067)
        ·
          refine ⟨23894411928883813344880601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15929607952589208896587067 23894411928883813344880601)
          ·
            refine ⟨17920808946662860008660451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23894411928883813344880601 17920808946662860008660451)
            ·
              refine ⟨26881213419994290012990677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17920808946662860008660451 26881213419994290012990677)
              ·
                refine ⟨630028439531116172179469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26881213419994290012990677 630028439531116172179469)
                ·
                  refine ⟨236260664824168564567301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 630028439531116172179469 236260664824168564567301)
                  ·
                    rfl

theorem cell21_1035261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_1035261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035261 prefixEnd_1035261 := by exact prefixLift 1035261
  have htrace : WordTrace (prefixWord ++ tailWord_1035261) baseStart_1035261 baseEnd_1035261 := by
    simpa [prefixWord, tailWord_1035261, baseEnd_1035261] using wordTrace_append hprefix tailTrace_1035261
  have hstable : (prefixWord ++ tailWord_1035261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035261).length < 2 ^ (prefixWord ++ tailWord_1035261).sum := by decide
  have hdescent : baseEnd_1035261 < baseStart_1035261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035275 : List Nat := [1, 1, 1, 1, 6, 2, 1, 4, 4]
def baseStart_1035275 : Nat := 118140960795 + 1035275 * 2 ^ 59
def prefixEnd_1035275 : Nat := 4983230072969 + 3 ^ 40 * 1035275 * 2
def baseEnd_1035275 : Nat := 236263859814907651333939

theorem tailTrace_1035275 : CollatzResearch.WordTrace tailWord_1035275 prefixEnd_1035275 236263859814907651333939 := by
  unfold tailWord_1035275
  simp only [CollatzResearch.WordTrace]
  refine ⟨37759581324382960738475279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25173054216255307158983519 37759581324382960738475279)
  ·
    refine ⟨56639371986574441107712919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37759581324382960738475279 56639371986574441107712919)
    ·
      refine ⟨84959057979861661661569379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56639371986574441107712919 84959057979861661661569379)
      ·
        refine ⟨127438586969792492492354069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84959057979861661661569379 127438586969792492492354069)
        ·
          refine ⟨5973683764209023085579097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 127438586969792492492354069 5973683764209023085579097)
          ·
            refine ⟨4480262823156767314184323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5973683764209023085579097 4480262823156767314184323)
            ·
              refine ⟨6720394234735150971276485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4480262823156767314184323 6720394234735150971276485)
              ·
                refine ⟨1260073919012840807114341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6720394234735150971276485 1260073919012840807114341)
                ·
                  refine ⟨236263859814907651333939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1260073919012840807114341 236263859814907651333939)
                  ·
                    rfl

theorem cell21_1035275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 4].length) (baseStart_1035275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035275 prefixEnd_1035275 := by exact prefixLift 1035275
  have htrace : WordTrace (prefixWord ++ tailWord_1035275) baseStart_1035275 baseEnd_1035275 := by
    simpa [prefixWord, tailWord_1035275, baseEnd_1035275] using wordTrace_append hprefix tailTrace_1035275
  have hstable : (prefixWord ++ tailWord_1035275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035275).length < 2 ^ (prefixWord ++ tailWord_1035275).sum := by decide
  have hdescent : baseEnd_1035275 < baseStart_1035275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035278 : List Nat := [4, 1, 1, 2, 2, 3, 1, 4, 3]
def baseStart_1035278 : Nat := 118140960795 + 1035278 * 2 ^ 59
def prefixEnd_1035278 : Nat := 4983230072969 + 3 ^ 40 * 1035278 * 2
def baseEnd_1035278 : Nat := 236264544455780312783933

theorem tailTrace_1035278 : CollatzResearch.WordTrace tailWord_1035278 prefixEnd_1035278 236264544455780312783933 := by
  unfold tailWord_1035278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4719961342921511531354311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25173127162248061500556325 4719961342921511531354311)
  ·
    refine ⟨7079942014382267297031467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4719961342921511531354311 7079942014382267297031467)
    ·
      refine ⟨10619913021573400945547201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7079942014382267297031467 10619913021573400945547201)
      ·
        refine ⟨7964934766180050709160401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10619913021573400945547201 7964934766180050709160401)
        ·
          refine ⟨5973701074635038031870301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7964934766180050709160401 5973701074635038031870301)
          ·
            refine ⟨2240137902988139261951363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5973701074635038031870301 2240137902988139261951363)
            ·
              refine ⟨3360206854482208892927045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2240137902988139261951363 3360206854482208892927045)
              ·
                refine ⟨630038785215414167423821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3360206854482208892927045 630038785215414167423821)
                ·
                  refine ⟨236264544455780312783933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 630038785215414167423821 236264544455780312783933)
                  ·
                    rfl

theorem cell21_1035278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_1035278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035278 prefixEnd_1035278 := by exact prefixLift 1035278
  have htrace : WordTrace (prefixWord ++ tailWord_1035278) baseStart_1035278 baseEnd_1035278 := by
    simpa [prefixWord, tailWord_1035278, baseEnd_1035278] using wordTrace_append hprefix tailTrace_1035278
  have hstable : (prefixWord ++ tailWord_1035278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035278).length < 2 ^ (prefixWord ++ tailWord_1035278).sum := by decide
  have hdescent : baseEnd_1035278 < baseStart_1035278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035289 : List Nat := [1, 2, 1, 2, 1, 1, 7, 6]
def baseStart_1035289 : Nat := 118140960795 + 1035289 * 2 ^ 59
def prefixEnd_1035289 : Nat := 4983230072969 + 3 ^ 40 * 1035289 * 2
def baseEnd_1035289 : Nat := 78755684935215579366859

theorem tailTrace_1035289 : CollatzResearch.WordTrace tailWord_1035289 prefixEnd_1035289 78755684935215579366859 := by
  unfold tailWord_1035289
  simp only [CollatzResearch.WordTrace]
  refine ⟨37760091946332241129484921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25173394630888160752989947 37760091946332241129484921)
  ·
    refine ⟨28320068959749180847113691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37760091946332241129484921 28320068959749180847113691)
    ·
      refine ⟨42480103439623771270670537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28320068959749180847113691 42480103439623771270670537)
      ·
        refine ⟨31860077579717828453002903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42480103439623771270670537 31860077579717828453002903)
        ·
          refine ⟨47790116369576742679504355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31860077579717828453002903 47790116369576742679504355)
          ·
            refine ⟨71685174554365114019256533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47790116369576742679504355 71685174554365114019256533)
            ·
              refine ⟨1680121278617932359826325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 71685174554365114019256533 1680121278617932359826325)
              ·
                refine ⟨78755684935215579366859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1680121278617932359826325 78755684935215579366859)
                ·
                  rfl

theorem cell21_1035289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 6].length) (baseStart_1035289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035289 prefixEnd_1035289 := by exact prefixLift 1035289
  have htrace : WordTrace (prefixWord ++ tailWord_1035289) baseStart_1035289 baseEnd_1035289 := by
    simpa [prefixWord, tailWord_1035289, baseEnd_1035289] using wordTrace_append hprefix tailTrace_1035289
  have hstable : (prefixWord ++ tailWord_1035289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035289).length < 2 ^ (prefixWord ++ tailWord_1035289).sum := by decide
  have hdescent : baseEnd_1035289 < baseStart_1035289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035357 : List Nat := [1, 4, 4, 1, 3, 1, 2, 5]
def baseStart_1035357 : Nat := 118140960795 + 1035357 * 2 ^ 59
def prefixEnd_1035357 : Nat := 4983230072969 + 3 ^ 40 * 1035357 * 2
def baseEnd_1035357 : Nat := 78760857777364576989035

theorem tailTrace_1035357 : CollatzResearch.WordTrace tailWord_1035357 prefixEnd_1035357 78760857777364576989035 := by
  unfold tailWord_1035357
  simp only [CollatzResearch.WordTrace]
  refine ⟨37762572110085888742960325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25175048073390592495306883 37762572110085888742960325)
  ·
    refine ⟨7080482270641104139305061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37762572110085888742960325 7080482270641104139305061)
    ·
      refine ⟨1327590425745207026119699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7080482270641104139305061 1327590425745207026119699)
      ·
        refine ⟨1991385638617810539179549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1327590425745207026119699 1991385638617810539179549)
        ·
          refine ⟨746769614481678952192331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1991385638617810539179549 746769614481678952192331)
          ·
            refine ⟨1120154421722518428288497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746769614481678952192331 1120154421722518428288497)
            ·
              refine ⟨840115816291888821216373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1120154421722518428288497 840115816291888821216373)
              ·
                refine ⟨78760857777364576989035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 840115816291888821216373 78760857777364576989035)
                ·
                  rfl

theorem cell21_1035357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 5].length) (baseStart_1035357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035357 prefixEnd_1035357 := by exact prefixLift 1035357
  have htrace : WordTrace (prefixWord ++ tailWord_1035357) baseStart_1035357 baseEnd_1035357 := by
    simpa [prefixWord, tailWord_1035357, baseEnd_1035357] using wordTrace_append hprefix tailTrace_1035357
  have hstable : (prefixWord ++ tailWord_1035357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035357).length < 2 ^ (prefixWord ++ tailWord_1035357).sum := by decide
  have hdescent : baseEnd_1035357 < baseStart_1035357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035365 : List Nat := [1, 3, 1, 3, 2, 1, 3, 7]
def baseStart_1035365 : Nat := 118140960795 + 1035365 * 2 ^ 59
def prefixEnd_1035365 : Nat := 4983230072969 + 3 ^ 40 * 1035365 * 2
def baseEnd_1035365 : Nat := 78761466347029164944585

theorem tailTrace_1035365 : CollatzResearch.WordTrace tailWord_1035365 prefixEnd_1035365 78761466347029164944585 := by
  unfold tailWord_1035365
  simp only [CollatzResearch.WordTrace]
  refine ⟨37762863894056906109251549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25175242596037937406167699 37762863894056906109251549)
  ·
    refine ⟨14161073960271339790969331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37762863894056906109251549 14161073960271339790969331)
    ·
      refine ⟨21241610940407009686453997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14161073960271339790969331 21241610940407009686453997)
      ·
        refine ⟨7965604102652628632420249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21241610940407009686453997 7965604102652628632420249)
        ·
          refine ⟨5974203076989471474315187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7965604102652628632420249 5974203076989471474315187)
          ·
            refine ⟨8961304615484207211472781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5974203076989471474315187 8961304615484207211472781)
            ·
              refine ⟨3360489230806577704302293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8961304615484207211472781 3360489230806577704302293)
              ·
                refine ⟨78761466347029164944585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3360489230806577704302293 78761466347029164944585)
                ·
                  rfl

theorem cell21_1035365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 7].length) (baseStart_1035365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035365 prefixEnd_1035365 := by exact prefixLift 1035365
  have htrace : WordTrace (prefixWord ++ tailWord_1035365) baseStart_1035365 baseEnd_1035365 := by
    simpa [prefixWord, tailWord_1035365, baseEnd_1035365] using wordTrace_append hprefix tailTrace_1035365
  have hstable : (prefixWord ++ tailWord_1035365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035365).length < 2 ^ (prefixWord ++ tailWord_1035365).sum := by decide
  have hdescent : baseEnd_1035365 < baseStart_1035365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035441 : List Nat := [1, 2, 2, 5, 1, 10]
def baseStart_1035441 : Nat := 118140960795 + 1035441 * 2 ^ 59
def prefixEnd_1035441 : Nat := 4983230072969 + 3 ^ 40 * 1035441 * 2
def baseEnd_1035441 : Nat := 8751916417649194502479

theorem tailTrace_1035441 : CollatzResearch.WordTrace tailWord_1035441 prefixEnd_1035441 8751916417649194502479 := by
  unfold tailWord_1035441
  simp only [CollatzResearch.WordTrace]
  refine ⟨37765635841781571089018177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25177090561187714059345451 37765635841781571089018177)
  ·
    refine ⟨28324226881336178316763633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37765635841781571089018177 28324226881336178316763633)
    ·
      refine ⟨21243170161002133737572725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28324226881336178316763633 21243170161002133737572725)
      ·
        refine ⟨1991547202593950037897443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21243170161002133737572725 1991547202593950037897443)
        ·
          refine ⟨2987320803890925056846165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991547202593950037897443 2987320803890925056846165)
          ·
            refine ⟨8751916417649194502479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2987320803890925056846165 8751916417649194502479)
            ·
              rfl

theorem cell21_1035441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 10].length) (baseStart_1035441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035441 prefixEnd_1035441 := by exact prefixLift 1035441
  have htrace : WordTrace (prefixWord ++ tailWord_1035441) baseStart_1035441 baseEnd_1035441 := by
    simpa [prefixWord, tailWord_1035441, baseEnd_1035441] using wordTrace_append hprefix tailTrace_1035441
  have hstable : (prefixWord ++ tailWord_1035441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035441).length < 2 ^ (prefixWord ++ tailWord_1035441).sum := by decide
  have hdescent : baseEnd_1035441 < baseStart_1035441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035489 : List Nat := [1, 2, 3, 1, 3, 2, 1, 5, 3]
def baseStart_1035489 : Nat := 118140960795 + 1035489 * 2 ^ 59
def prefixEnd_1035489 : Nat := 4983230072969 + 3 ^ 40 * 1035489 * 2
def baseEnd_1035489 : Nat := 236312697530490834766835

theorem tailTrace_1035489 : CollatzResearch.WordTrace tailWord_1035489 prefixEnd_1035489 236312697530490834766835 := by
  unfold tailWord_1035489
  simp only [CollatzResearch.WordTrace]
  refine ⟨37767386545607675286765521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25178257697071783524510347 37767386545607675286765521)
  ·
    refine ⟨28325539909205756465074141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37767386545607675286765521 28325539909205756465074141)
    ·
      refine ⟨10622077465952158674402803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28325539909205756465074141 10622077465952158674402803)
      ·
        refine ⟨15933116198928238011604205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10622077465952158674402803 15933116198928238011604205)
        ·
          refine ⟨5974918574598089254351577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15933116198928238011604205 5974918574598089254351577)
          ·
            refine ⟨4481188930948566940763683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5974918574598089254351577 4481188930948566940763683)
            ·
              refine ⟨6721783396422850411145525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4481188930948566940763683 6721783396422850411145525)
              ·
                refine ⟨630167193414642226044893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6721783396422850411145525 630167193414642226044893)
                ·
                  refine ⟨236312697530490834766835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 630167193414642226044893 236312697530490834766835)
                  ·
                    rfl

theorem cell21_1035489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 3].length) (baseStart_1035489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035489 prefixEnd_1035489 := by exact prefixLift 1035489
  have htrace : WordTrace (prefixWord ++ tailWord_1035489) baseStart_1035489 baseEnd_1035489 := by
    simpa [prefixWord, tailWord_1035489, baseEnd_1035489] using wordTrace_append hprefix tailTrace_1035489
  have hstable : (prefixWord ++ tailWord_1035489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035489).length < 2 ^ (prefixWord ++ tailWord_1035489).sum := by decide
  have hdescent : baseEnd_1035489 < baseStart_1035489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035503 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 6]
def baseStart_1035503 : Nat := 118140960795 + 1035503 * 2 ^ 59
def prefixEnd_1035503 : Nat := 4983230072969 + 3 ^ 40 * 1035503 * 2
def baseEnd_1035503 : Nat := 236315892521229921533473

theorem tailTrace_1035503 : CollatzResearch.WordTrace tailWord_1035503 prefixEnd_1035503 236315892521229921533473 := by
  unfold tailWord_1035503
  simp only [CollatzResearch.WordTrace]
  refine ⟨37767897167556955677775163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25178598111704637118516775 37767897167556955677775163)
  ·
    refine ⟨56651845751335433516662745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37767897167556955677775163 56651845751335433516662745)
    ·
      refine ⟨42488884313501575137497059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56651845751335433516662745 42488884313501575137497059)
      ·
        refine ⟨63733326470252362706245589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42488884313501575137497059 63733326470252362706245589)
        ·
          refine ⟨1493749839146539750927631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 63733326470252362706245589 1493749839146539750927631)
          ·
            refine ⟨2240624758719809626391447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1493749839146539750927631 2240624758719809626391447)
            ·
              refine ⟨3360937138079714439587171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2240624758719809626391447 3360937138079714439587171)
              ·
                refine ⟨5041405707119571659380757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3360937138079714439587171 5041405707119571659380757)
                ·
                  refine ⟨236315892521229921533473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5041405707119571659380757 236315892521229921533473)
                  ·
                    rfl

theorem cell21_1035503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 6].length) (baseStart_1035503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035503 prefixEnd_1035503 := by exact prefixLift 1035503
  have htrace : WordTrace (prefixWord ++ tailWord_1035503) baseStart_1035503 baseEnd_1035503 := by
    simpa [prefixWord, tailWord_1035503, baseEnd_1035503] using wordTrace_append hprefix tailTrace_1035503
  have hstable : (prefixWord ++ tailWord_1035503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035503).length < 2 ^ (prefixWord ++ tailWord_1035503).sum := by decide
  have hdescent : baseEnd_1035503 < baseStart_1035503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035534 : List Nat := [4, 1, 1, 2, 1, 3, 4, 5]
def baseStart_1035534 : Nat := 118140960795 + 1035534 * 2 ^ 59
def prefixEnd_1035534 : Nat := 4983230072969 + 3 ^ 40 * 1035534 * 2
def baseEnd_1035534 : Nat := 78774322381193585505581

theorem tailTrace_1035534 : CollatzResearch.WordTrace tailWord_1035534 prefixEnd_1035534 78774322381193585505581 := by
  unfold tailWord_1035534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4721128478805580996519207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25179351886963098648102437 4721128478805580996519207)
  ·
    refine ⟨7081692718208371494778811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4721128478805580996519207 7081692718208371494778811)
    ·
      refine ⟨10622539077312557242168217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7081692718208371494778811 10622539077312557242168217)
      ·
        refine ⟨7966904307984417931626163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10622539077312557242168217 7966904307984417931626163)
        ·
          refine ⟨11950356461976626897439245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7966904307984417931626163 11950356461976626897439245)
          ·
            refine ⟨4481383673241235086539717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11950356461976626897439245 4481383673241235086539717)
            ·
              refine ⟨840259438732731578726197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4481383673241235086539717 840259438732731578726197)
              ·
                refine ⟨78774322381193585505581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 840259438732731578726197 78774322381193585505581)
                ·
                  rfl

theorem cell21_1035534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_1035534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035534 prefixEnd_1035534 := by exact prefixLift 1035534
  have htrace : WordTrace (prefixWord ++ tailWord_1035534) baseStart_1035534 baseEnd_1035534 := by
    simpa [prefixWord, tailWord_1035534, baseEnd_1035534] using wordTrace_append hprefix tailTrace_1035534
  have hstable : (prefixWord ++ tailWord_1035534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035534).length < 2 ^ (prefixWord ++ tailWord_1035534).sum := by decide
  have hdescent : baseEnd_1035534 < baseStart_1035534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035734 : List Nat := [5, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_1035734 : Nat := 118140960795 + 1035734 * 2 ^ 59
def prefixEnd_1035734 : Nat := 4983230072969 + 3 ^ 40 * 1035734 * 2
def baseEnd_1035734 : Nat := 236368609868424853183001

theorem tailTrace_1035734 : CollatzResearch.WordTrace tailWord_1035734 prefixEnd_1035734 236368609868424853183001 := by
  unfold tailWord_1035734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2361020151857505133089641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25184214953146721419622837 2361020151857505133089641)
  ·
    refine ⟨1770765113893128849817231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2361020151857505133089641 1770765113893128849817231)
    ·
      refine ⟨2656147670839693274725847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1770765113893128849817231 2656147670839693274725847)
      ·
        refine ⟨3984221506259539912088771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2656147670839693274725847 3984221506259539912088771)
        ·
          refine ⟨5976332259389309868133157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3984221506259539912088771 5976332259389309868133157)
          ·
            refine ⟨1120562298635495600274967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5976332259389309868133157 1120562298635495600274967)
            ·
              refine ⟨1680843447953243400412451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120562298635495600274967 1680843447953243400412451)
              ·
                refine ⟨2521265171929865100618677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1680843447953243400412451 2521265171929865100618677)
                ·
                  refine ⟨236368609868424853183001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2521265171929865100618677 236368609868424853183001)
                  ·
                    rfl

theorem cell21_1035734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_1035734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035734 prefixEnd_1035734 := by exact prefixLift 1035734
  have htrace : WordTrace (prefixWord ++ tailWord_1035734) baseStart_1035734 baseEnd_1035734 := by
    simpa [prefixWord, tailWord_1035734, baseEnd_1035734] using wordTrace_append hprefix tailTrace_1035734
  have hstable : (prefixWord ++ tailWord_1035734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035734).length < 2 ^ (prefixWord ++ tailWord_1035734).sum := by decide
  have hdescent : baseEnd_1035734 < baseStart_1035734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035745 : List Nat := [1, 2, 3, 1, 2, 4, 2, 6]
def baseStart_1035745 : Nat := 118140960795 + 1035745 * 2 ^ 59
def prefixEnd_1035745 : Nat := 4983230072969 + 3 ^ 40 * 1035745 * 2
def baseEnd_1035745 : Nat := 78790373406097092833215

theorem tailTrace_1035745 : CollatzResearch.WordTrace tailWord_1035745 prefixEnd_1035745 78790373406097092833215 := by
  unfold tailWord_1035745
  simp only [CollatzResearch.WordTrace]
  refine ⟨37776723632680231008084689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25184482421786820672056459 37776723632680231008084689)
  ·
    refine ⟨28332542724510173256063517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37776723632680231008084689 28332542724510173256063517)
    ·
      refine ⟨10624703521691314971023819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28332542724510173256063517 10624703521691314971023819)
      ·
        refine ⟨15937055282536972456535729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10624703521691314971023819 15937055282536972456535729)
        ·
          refine ⟨11952791461902729342401797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15937055282536972456535729 11952791461902729342401797)
          ·
            refine ⟨2241148399106761751700337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11952791461902729342401797 2241148399106761751700337)
            ·
              refine ⟨1680861299330071313775253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2241148399106761751700337 1680861299330071313775253)
              ·
                refine ⟨78790373406097092833215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1680861299330071313775253 78790373406097092833215)
                ·
                  rfl

theorem cell21_1035745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 6].length) (baseStart_1035745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035745 prefixEnd_1035745 := by exact prefixLift 1035745
  have htrace : WordTrace (prefixWord ++ tailWord_1035745) baseStart_1035745 baseEnd_1035745 := by
    simpa [prefixWord, tailWord_1035745, baseEnd_1035745] using wordTrace_append hprefix tailTrace_1035745
  have hstable : (prefixWord ++ tailWord_1035745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035745).length < 2 ^ (prefixWord ++ tailWord_1035745).sum := by decide
  have hdescent : baseEnd_1035745 < baseStart_1035745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035759 : List Nat := [1, 1, 2, 1, 4, 1, 2, 4, 5]
def baseStart_1035759 : Nat := 118140960795 + 1035759 * 2 ^ 59
def prefixEnd_1035759 : Nat := 4983230072969 + 3 ^ 40 * 1035759 * 2
def baseEnd_1035759 : Nat := 236374315209030365266283

theorem tailTrace_1035759 : CollatzResearch.WordTrace tailWord_1035759 prefixEnd_1035759 236374315209030365266283 := by
  unfold tailWord_1035759
  simp only [CollatzResearch.WordTrace]
  refine ⟨37777234254629511399094331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25184822836419674266062887 37777234254629511399094331)
  ·
    refine ⟨56665851381944267098641497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37777234254629511399094331 56665851381944267098641497)
    ·
      refine ⟨42499388536458200323981123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56665851381944267098641497 42499388536458200323981123)
      ·
        refine ⟨63749082804687300485971685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42499388536458200323981123 63749082804687300485971685)
        ·
          refine ⟨11952953025878868841119691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63749082804687300485971685 11952953025878868841119691)
          ·
            refine ⟨17929429538818303261679537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11952953025878868841119691 17929429538818303261679537)
            ·
              refine ⟨13447072154113727446259653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17929429538818303261679537 13447072154113727446259653)
              ·
                refine ⟨2521326028896323896173685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13447072154113727446259653 2521326028896323896173685)
                ·
                  refine ⟨236374315209030365266283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2521326028896323896173685 236374315209030365266283)
                  ·
                    rfl

theorem cell21_1035759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 5].length) (baseStart_1035759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035759 prefixEnd_1035759 := by exact prefixLift 1035759
  have htrace : WordTrace (prefixWord ++ tailWord_1035759) baseStart_1035759 baseEnd_1035759 := by
    simpa [prefixWord, tailWord_1035759, baseEnd_1035759] using wordTrace_append hprefix tailTrace_1035759
  have hstable : (prefixWord ++ tailWord_1035759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035759).length < 2 ^ (prefixWord ++ tailWord_1035759).sum := by decide
  have hdescent : baseEnd_1035759 < baseStart_1035759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035796 : List Nat := [2, 4, 3, 1, 3, 1, 1, 6]
def baseStart_1035796 : Nat := 118140960795 + 1035796 * 2 ^ 59
def prefixEnd_1035796 : Nat := 4983230072969 + 3 ^ 40 * 1035796 * 2
def baseEnd_1035796 : Nat := 78794253037708841049847

theorem tailTrace_1035796 : CollatzResearch.WordTrace tailWord_1035796 prefixEnd_1035796 78794253037708841049847 := by
  unfold tailWord_1035796
  simp only [CollatzResearch.WordTrace]
  refine ⟨18889291877747733359095621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25185722503663644478794161 18889291877747733359095621)
  ·
    refine ⟨3541742227077700004830429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18889291877747733359095621 3541742227077700004830429)
    ·
      refine ⟨1328153335154137501811411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3541742227077700004830429 1328153335154137501811411)
      ·
        refine ⟨1992230002731206252717117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1328153335154137501811411 1992230002731206252717117)
        ·
          refine ⟨747086251024202344768919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1992230002731206252717117 747086251024202344768919)
          ·
            refine ⟨1120629376536303517153379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747086251024202344768919 1120629376536303517153379)
            ·
              refine ⟨1680944064804455275730069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120629376536303517153379 1680944064804455275730069)
              ·
                refine ⟨78794253037708841049847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1680944064804455275730069 78794253037708841049847)
                ·
                  rfl

theorem cell21_1035796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 6].length) (baseStart_1035796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035796 prefixEnd_1035796 := by exact prefixLift 1035796
  have htrace : WordTrace (prefixWord ++ tailWord_1035796) baseStart_1035796 baseEnd_1035796 := by
    simpa [prefixWord, tailWord_1035796, baseEnd_1035796] using wordTrace_append hprefix tailTrace_1035796
  have hstable : (prefixWord ++ tailWord_1035796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035796).length < 2 ^ (prefixWord ++ tailWord_1035796).sum := by decide
  have hdescent : baseEnd_1035796 < baseStart_1035796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035852 : List Nat := [2, 2, 1, 3, 1, 4, 2, 1, 5]
def baseStart_1035852 : Nat := 118140960795 + 1035852 * 2 ^ 59
def prefixEnd_1035852 : Nat := 4983230072969 + 3 ^ 40 * 1035852 * 2
def baseEnd_1035852 : Nat := 236395539076082870216093

theorem tailTrace_1035852 : CollatzResearch.WordTrace tailWord_1035852 prefixEnd_1035852 236395539076082870216093 := by
  unfold tailWord_1035852
  simp only [CollatzResearch.WordTrace]
  refine ⟨18890313121646294141114905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25187084162195058854819873 18890313121646294141114905)
  ·
    refine ⟨14167734841234720605836179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18890313121646294141114905 14167734841234720605836179)
    ·
      refine ⟨21251602261852080908754269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14167734841234720605836179 21251602261852080908754269)
      ·
        refine ⟨7969350848194530340782851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21251602261852080908754269 7969350848194530340782851)
        ·
          refine ⟨11954026272291795511174277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7969350848194530340782851 11954026272291795511174277)
          ·
            refine ⟨2241379926054711658345177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11954026272291795511174277 2241379926054711658345177)
            ·
              refine ⟨1681034944541033743758883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2241379926054711658345177 1681034944541033743758883)
              ·
                refine ⟨2521552416811550615638325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1681034944541033743758883 2521552416811550615638325)
                ·
                  refine ⟨236395539076082870216093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2521552416811550615638325 236395539076082870216093)
                  ·
                    rfl

theorem cell21_1035852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_1035852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035852 prefixEnd_1035852 := by exact prefixLift 1035852
  have htrace : WordTrace (prefixWord ++ tailWord_1035852) baseStart_1035852 baseEnd_1035852 := by
    simpa [prefixWord, tailWord_1035852, baseEnd_1035852] using wordTrace_append hprefix tailTrace_1035852
  have hstable : (prefixWord ++ tailWord_1035852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035852).length < 2 ^ (prefixWord ++ tailWord_1035852).sum := by decide
  have hdescent : baseEnd_1035852 < baseStart_1035852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035866 : List Nat := [3, 1, 1, 2, 1, 1, 1, 7, 4]
def baseStart_1035866 : Nat := 118140960795 + 1035866 * 2 ^ 59
def prefixEnd_1035866 : Nat := 4983230072969 + 3 ^ 40 * 1035866 * 2
def baseEnd_1035866 : Nat := 236398734066821956982731

theorem tailTrace_1035866 : CollatzResearch.WordTrace tailWord_1035866 prefixEnd_1035866 236398734066821956982731 := by
  unfold tailWord_1035866
  simp only [CollatzResearch.WordTrace]
  refine ⟨9445284216310467168309863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25187424576827912448826301 9445284216310467168309863)
  ·
    refine ⟨14167926324465700752464795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9445284216310467168309863 14167926324465700752464795)
    ·
      refine ⟨21251889486698551128697193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14167926324465700752464795 21251889486698551128697193)
      ·
        refine ⟨15938917115023913346522895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21251889486698551128697193 15938917115023913346522895)
        ·
          refine ⟨23908375672535870019784343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15938917115023913346522895 23908375672535870019784343)
          ·
            refine ⟨35862563508803805029676515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23908375672535870019784343 35862563508803805029676515)
            ·
              refine ⟨53793845263205707544514773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35862563508803805029676515 53793845263205707544514773)
              ·
                refine ⟨1260793248356383770574565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53793845263205707544514773 1260793248356383770574565)
                ·
                  refine ⟨236398734066821956982731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1260793248356383770574565 236398734066821956982731)
                  ·
                    rfl

theorem cell21_1035866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_1035866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035866 prefixEnd_1035866 := by exact prefixLift 1035866
  have htrace : WordTrace (prefixWord ++ tailWord_1035866) baseStart_1035866 baseEnd_1035866 := by
    simpa [prefixWord, tailWord_1035866, baseEnd_1035866] using wordTrace_append hprefix tailTrace_1035866
  have hstable : (prefixWord ++ tailWord_1035866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035866).length < 2 ^ (prefixWord ++ tailWord_1035866).sum := by decide
  have hdescent : baseEnd_1035866 < baseStart_1035866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035956 : List Nat := [2, 5, 14]
def baseStart_1035956 : Nat := 118140960795 + 1035956 * 2 ^ 59
def prefixEnd_1035956 : Nat := 4983230072969 + 3 ^ 40 * 1035956 * 2
def baseEnd_1035956 : Nat := 324306273378603292843

theorem tailTrace_1035956 : CollatzResearch.WordTrace tailWord_1035956 prefixEnd_1035956 324306273378603292843 := by
  unfold tailWord_1035956
  simp only [CollatzResearch.WordTrace]
  refine ⟨18892209717457907022007861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25189612956610542696010481 18892209717457907022007861)
  ·
    refine ⟨1771144661011678783313237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18892209717457907022007861 1771144661011678783313237)
    ·
      refine ⟨324306273378603292843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 14 1771144661011678783313237 324306273378603292843)
      ·
        rfl

theorem cell21_1035956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 14].length) (baseStart_1035956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035956 prefixEnd_1035956 := by exact prefixLift 1035956
  have htrace : WordTrace (prefixWord ++ tailWord_1035956) baseStart_1035956 baseEnd_1035956 := by
    simpa [prefixWord, tailWord_1035956, baseEnd_1035956] using wordTrace_append hprefix tailTrace_1035956
  have hstable : (prefixWord ++ tailWord_1035956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035956).length < 2 ^ (prefixWord ++ tailWord_1035956).sum := by decide
  have hdescent : baseEnd_1035956 < baseStart_1035956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035959 : List Nat := [1, 1, 3, 1, 5, 2, 2, 2, 4]
def baseStart_1035959 : Nat := 118140960795 + 1035959 * 2 ^ 59
def prefixEnd_1035959 : Nat := 4983230072969 + 3 ^ 40 * 1035959 * 2
def baseEnd_1035959 : Nat := 236419957933874461932541

theorem tailTrace_1035959 : CollatzResearch.WordTrace tailWord_1035959 prefixEnd_1035959 236419957933874461932541 := by
  unfold tailWord_1035959
  simp only [CollatzResearch.WordTrace]
  refine ⟨37784528853904945556374931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25189685902603297037583287 37784528853904945556374931)
  ·
    refine ⟨56676793280857418334562397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37784528853904945556374931 56676793280857418334562397)
    ·
      refine ⟨21253797480321531875460899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56676793280857418334562397 21253797480321531875460899)
      ·
        refine ⟨31880696220482297813191349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21253797480321531875460899 31880696220482297813191349)
        ·
          refine ⟨2988815270670215419986689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31880696220482297813191349 2988815270670215419986689)
          ·
            refine ⟨2241611453002661564990017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2988815270670215419986689 2241611453002661564990017)
            ·
              refine ⟨1681208589751996173742513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2241611453002661564990017 1681208589751996173742513)
              ·
                refine ⟨1260906442313997130306885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1681208589751996173742513 1260906442313997130306885)
                ·
                  refine ⟨236419957933874461932541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1260906442313997130306885 236419957933874461932541)
                  ·
                    rfl

theorem cell21_1035959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 4].length) (baseStart_1035959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035959 prefixEnd_1035959 := by exact prefixLift 1035959
  have htrace : WordTrace (prefixWord ++ tailWord_1035959) baseStart_1035959 baseEnd_1035959 := by
    simpa [prefixWord, tailWord_1035959, baseEnd_1035959] using wordTrace_append hprefix tailTrace_1035959
  have hstable : (prefixWord ++ tailWord_1035959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035959).length < 2 ^ (prefixWord ++ tailWord_1035959).sum := by decide
  have hdescent : baseEnd_1035959 < baseStart_1035959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035962 : List Nat := [3, 1, 1, 1, 2, 6, 2, 2, 3]
def baseStart_1035962 : Nat := 118140960795 + 1035962 * 2 ^ 59
def prefixEnd_1035962 : Nat := 4983230072969 + 3 ^ 40 * 1035962 * 2
def baseEnd_1035962 : Nat := 236420642574747123382535

theorem tailTrace_1035962 : CollatzResearch.WordTrace tailWord_1035962 prefixEnd_1035962 236420642574747123382535 := by
  unfold tailWord_1035962
  simp only [CollatzResearch.WordTrace]
  refine ⟨9446159568223519267183535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25189758848596051379156093 9446159568223519267183535)
  ·
    refine ⟨14169239352335278900775303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9446159568223519267183535 14169239352335278900775303)
    ·
      refine ⟨21253859028502918351162955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14169239352335278900775303 21253859028502918351162955)
      ·
        refine ⟨31880788542754377526744433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21253859028502918351162955 31880788542754377526744433)
        ·
          refine ⟨23910591407065783145058325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31880788542754377526744433 23910591407065783145058325)
          ·
            refine ⟨1120808972206208584924609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23910591407065783145058325 1120808972206208584924609)
            ·
              refine ⟨840606729154656438693457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1120808972206208584924609 840606729154656438693457)
              ·
                refine ⟨630455046865992329020093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840606729154656438693457 630455046865992329020093)
                ·
                  refine ⟨236420642574747123382535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 630455046865992329020093 236420642574747123382535)
                  ·
                    rfl

theorem cell21_1035962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_1035962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1035962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1035962 prefixEnd_1035962 := by exact prefixLift 1035962
  have htrace : WordTrace (prefixWord ++ tailWord_1035962) baseStart_1035962 baseEnd_1035962 := by
    simpa [prefixWord, tailWord_1035962, baseEnd_1035962] using wordTrace_append hprefix tailTrace_1035962
  have hstable : (prefixWord ++ tailWord_1035962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035962).length < 2 ^ (prefixWord ++ tailWord_1035962).sum := by decide
  have hdescent : baseEnd_1035962 < baseStart_1035962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036018 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 6]
def baseStart_1036018 : Nat := 118140960795 + 1036018 * 2 ^ 59
def prefixEnd_1036018 : Nat := 4983230072969 + 3 ^ 40 * 1036018 * 2
def baseEnd_1036018 : Nat := 236433422537703470449087

theorem tailTrace_1036018 : CollatzResearch.WordTrace tailWord_1036018 prefixEnd_1036018 236433422537703470449087 := by
  unfold tailWord_1036018
  simp only [CollatzResearch.WordTrace]
  refine ⟨9446670190172799658193177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25191120507127465755181805 9446670190172799658193177)
  ·
    refine ⟨7085002642629599743644883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9446670190172799658193177 7085002642629599743644883)
    ·
      refine ⟨10627503963944399615467325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7085002642629599743644883 10627503963944399615467325)
      ·
        refine ⟨3985313986479149855800247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10627503963944399615467325 3985313986479149855800247)
        ·
          refine ⟨5977970979718724783700371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3985313986479149855800247 5977970979718724783700371)
          ·
            refine ⟨8966956469578087175550557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5977970979718724783700371 8966956469578087175550557)
            ·
              refine ⟨3362608676091782690831459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8966956469578087175550557 3362608676091782690831459)
              ·
                refine ⟨5043913014137674036247189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3362608676091782690831459 5043913014137674036247189)
                ·
                  refine ⟨236433422537703470449087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5043913014137674036247189 236433422537703470449087)
                  ·
                    rfl

theorem cell21_1036018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_1036018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036018 prefixEnd_1036018 := by exact prefixLift 1036018
  have htrace : WordTrace (prefixWord ++ tailWord_1036018) baseStart_1036018 baseEnd_1036018 := by
    simpa [prefixWord, tailWord_1036018, baseEnd_1036018] using wordTrace_append hprefix tailTrace_1036018
  have hstable : (prefixWord ++ tailWord_1036018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036018).length < 2 ^ (prefixWord ++ tailWord_1036018).sum := by decide
  have hdescent : baseEnd_1036018 < baseStart_1036018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036131 : List Nat := [1, 1, 1, 5, 5, 1, 2, 2, 3]
def baseStart_1036131 : Nat := 118140960795 + 1036131 * 2 ^ 59
def prefixEnd_1036131 : Nat := 4983230072969 + 3 ^ 40 * 1036131 * 2
def baseEnd_1036131 : Nat := 236459210677240385065523

theorem tailTrace_1036131 : CollatzResearch.WordTrace tailWord_1036131 prefixEnd_1036131 236459210677240385065523 := by
  unfold tailWord_1036131
  simp only [CollatzResearch.WordTrace]
  refine ⟨37790802209281818931636247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25193868139521212621090831 37790802209281818931636247)
  ·
    refine ⟨56686203313922728397454371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37790802209281818931636247 56686203313922728397454371)
    ·
      refine ⟨85029304970884092596181557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56686203313922728397454371 85029304970884092596181557)
      ·
        refine ⟨7971497341020383680892021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85029304970884092596181557 7971497341020383680892021)
        ·
          refine ⟨747327875720660970083627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7971497341020383680892021 747327875720660970083627)
          ·
            refine ⟨1120991813580991455125441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747327875720660970083627 1120991813580991455125441)
            ·
              refine ⟨840743860185743591344081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1120991813580991455125441 840743860185743591344081)
              ·
                refine ⟨630557895139307693508061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840743860185743591344081 630557895139307693508061)
                ·
                  refine ⟨236459210677240385065523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 630557895139307693508061 236459210677240385065523)
                  ·
                    rfl

theorem cell21_1036131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 3].length) (baseStart_1036131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036131 prefixEnd_1036131 := by exact prefixLift 1036131
  have htrace : WordTrace (prefixWord ++ tailWord_1036131) baseStart_1036131 baseEnd_1036131 := by
    simpa [prefixWord, tailWord_1036131, baseEnd_1036131] using wordTrace_append hprefix tailTrace_1036131
  have hstable : (prefixWord ++ tailWord_1036131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036131).length < 2 ^ (prefixWord ++ tailWord_1036131).sum := by decide
  have hdescent : baseEnd_1036131 < baseStart_1036131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036142 : List Nat := [4, 1, 2, 3, 1, 3, 1, 6]
def baseStart_1036142 : Nat := 118140960795 + 1036142 * 2 ^ 59
def prefixEnd_1036142 : Nat := 4983230072969 + 3 ^ 40 * 1036142 * 2
def baseEnd_1036142 : Nat := 78820573675702270127389

theorem tailTrace_1036142 : CollatzResearch.WordTrace tailWord_1036142 prefixEnd_1036142 78820573675702270127389 := by
  unfold tailWord_1036142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4723900426530245976285835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25194135608161311873524453 4723900426530245976285835)
  ·
    refine ⟨7085850639795368964428753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4723900426530245976285835 7085850639795368964428753)
    ·
      refine ⟨5314387979846526723321565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7085850639795368964428753 5314387979846526723321565)
      ·
        refine ⟨1992895492442447521245587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5314387979846526723321565 1992895492442447521245587)
        ·
          refine ⟨2989343238663671281868381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1992895492442447521245587 2989343238663671281868381)
          ·
            refine ⟨1121003714498876730700643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2989343238663671281868381 1121003714498876730700643)
            ·
              refine ⟨1681505571748315096050965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121003714498876730700643 1681505571748315096050965)
              ·
                refine ⟨78820573675702270127389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1681505571748315096050965 78820573675702270127389)
                ·
                  rfl

theorem cell21_1036142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_1036142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036142 prefixEnd_1036142 := by exact prefixLift 1036142
  have htrace : WordTrace (prefixWord ++ tailWord_1036142) baseStart_1036142 baseEnd_1036142 := by
    simpa [prefixWord, tailWord_1036142, baseEnd_1036142] using wordTrace_append hprefix tailTrace_1036142
  have hstable : (prefixWord ++ tailWord_1036142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036142).length < 2 ^ (prefixWord ++ tailWord_1036142).sum := by decide
  have hdescent : baseEnd_1036142 < baseStart_1036142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036190 : List Nat := [4, 3, 1, 3, 1, 1, 2, 1, 5]
def baseStart_1036190 : Nat := 118140960795 + 1036190 * 2 ^ 59
def prefixEnd_1036190 : Nat := 4983230072969 + 3 ^ 40 * 1036190 * 2
def baseEnd_1036190 : Nat := 236472675281069393582069

theorem tailTrace_1036190 : CollatzResearch.WordTrace tailWord_1036190 prefixEnd_1036190 236472675281069393582069 := by
  unfold tailWord_1036190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4724119264508509001004253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25195302744045381338689349 4724119264508509001004253)
  ·
    refine ⟨1771544724190690875376595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4724119264508509001004253 1771544724190690875376595)
    ·
      refine ⟨2657317086286036313064893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1771544724190690875376595 2657317086286036313064893)
      ·
        refine ⟨996493907357263617399335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2657317086286036313064893 996493907357263617399335)
        ·
          refine ⟨1494740861035895426099003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996493907357263617399335 1494740861035895426099003)
          ·
            refine ⟨2242111291553843139148505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494740861035895426099003 2242111291553843139148505)
            ·
              refine ⟨1681583468665382354361379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2242111291553843139148505 1681583468665382354361379)
              ·
                refine ⟨2522375202998073531542069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1681583468665382354361379 2522375202998073531542069)
                ·
                  refine ⟨236472675281069393582069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2522375202998073531542069 236472675281069393582069)
                  ·
                    rfl

theorem cell21_1036190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_1036190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036190 prefixEnd_1036190 := by exact prefixLift 1036190
  have htrace : WordTrace (prefixWord ++ tailWord_1036190) baseStart_1036190 baseEnd_1036190 := by
    simpa [prefixWord, tailWord_1036190, baseEnd_1036190] using wordTrace_append hprefix tailTrace_1036190
  have hstable : (prefixWord ++ tailWord_1036190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036190).length < 2 ^ (prefixWord ++ tailWord_1036190).sum := by decide
  have hdescent : baseEnd_1036190 < baseStart_1036190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036249 : List Nat := [1, 2, 1, 2, 7, 1, 1, 1, 5]
def baseStart_1036249 : Nat := 118140960795 + 1036249 * 2 ^ 59
def prefixEnd_1036249 : Nat := 4983230072969 + 3 ^ 40 * 1036249 * 2
def baseEnd_1036249 : Nat := 236486139884898402098615

theorem tailTrace_1036249 : CollatzResearch.WordTrace tailWord_1036249 prefixEnd_1036249 236486139884898402098615 := by
  unfold tailWord_1036249
  simp only [CollatzResearch.WordTrace]
  refine ⟨37795106022854325084431801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25196737348569550056287867 37795106022854325084431801)
  ·
    refine ⟨28346329517140743813323851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37795106022854325084431801 28346329517140743813323851)
    ·
      refine ⟨42519494275711115719985777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28346329517140743813323851 42519494275711115719985777)
      ·
        refine ⟨31889620706783336789989333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42519494275711115719985777 31889620706783336789989333)
        ·
          refine ⟨747412985315234456015375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 31889620706783336789989333 747412985315234456015375)
          ·
            refine ⟨1121119477972851684023063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747412985315234456015375 1121119477972851684023063)
            ·
              refine ⟨1681679216959277526034595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121119477972851684023063 1681679216959277526034595)
              ·
                refine ⟨2522518825438916289051893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1681679216959277526034595 2522518825438916289051893)
                ·
                  refine ⟨236486139884898402098615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2522518825438916289051893 236486139884898402098615)
                  ·
                    rfl

theorem cell21_1036249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 5].length) (baseStart_1036249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036249 prefixEnd_1036249 := by exact prefixLift 1036249
  have htrace : WordTrace (prefixWord ++ tailWord_1036249) baseStart_1036249 baseEnd_1036249 := by
    simpa [prefixWord, tailWord_1036249, baseEnd_1036249] using wordTrace_append hprefix tailTrace_1036249
  have hstable : (prefixWord ++ tailWord_1036249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036249).length < 2 ^ (prefixWord ++ tailWord_1036249).sum := by decide
  have hdescent : baseEnd_1036249 < baseStart_1036249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036260 : List Nat := [2, 3, 1, 1, 1, 1, 6, 6]
def baseStart_1036260 : Nat := 118140960795 + 1036260 * 2 ^ 59
def prefixEnd_1036260 : Nat := 4983230072969 + 3 ^ 40 * 1036260 * 2
def baseEnd_1036260 : Nat := 78829550078254942471753

theorem tailTrace_1036260 : CollatzResearch.WordTrace tailWord_1036260 prefixEnd_1036260 78829550078254942471753 := by
  unfold tailWord_1036260
  simp only [CollatzResearch.WordTrace]
  refine ⟨18897753612907236981541117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25197004817209649308721489 18897753612907236981541117)
  ·
    refine ⟨7086657604840213868077919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18897753612907236981541117 7086657604840213868077919)
    ·
      refine ⟨10629986407260320802116879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7086657604840213868077919 10629986407260320802116879)
      ·
        refine ⟨15944979610890481203175319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10629986407260320802116879 15944979610890481203175319)
        ·
          refine ⟨23917469416335721804762979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15944979610890481203175319 23917469416335721804762979)
          ·
            refine ⟨35876204124503582707144469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23917469416335721804762979 35876204124503582707144469)
            ·
              refine ⟨1681697068336105439397397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35876204124503582707144469 1681697068336105439397397)
              ·
                refine ⟨78829550078254942471753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1681697068336105439397397 78829550078254942471753)
                ·
                  rfl

theorem cell21_1036260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 6].length) (baseStart_1036260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036260 prefixEnd_1036260 := by exact prefixLift 1036260
  have htrace : WordTrace (prefixWord ++ tailWord_1036260) baseStart_1036260 baseEnd_1036260 := by
    simpa [prefixWord, tailWord_1036260, baseEnd_1036260] using wordTrace_append hprefix tailTrace_1036260
  have hstable : (prefixWord ++ tailWord_1036260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036260).length < 2 ^ (prefixWord ++ tailWord_1036260).sum := by decide
  have hdescent : baseEnd_1036260 < baseStart_1036260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036263 : List Nat := [1, 1, 5, 2, 3, 1, 1, 3, 4]
def baseStart_1036263 : Nat := 118140960795 + 1036263 * 2 ^ 59
def prefixEnd_1036263 : Nat := 4983230072969 + 3 ^ 40 * 1036263 * 2
def baseEnd_1036263 : Nat := 236489334875637488865253

theorem tailTrace_1036263 : CollatzResearch.WordTrace tailWord_1036263 prefixEnd_1036263 236489334875637488865253 := by
  unfold tailWord_1036263
  simp only [CollatzResearch.WordTrace]
  refine ⟨37795616644803605475441443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25197077763202403650294295 37795616644803605475441443)
  ·
    refine ⟨56693424967205408213162165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37795616644803605475441443 56693424967205408213162165)
    ·
      refine ⟨5315008590675507019983953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56693424967205408213162165 5315008590675507019983953)
      ·
        refine ⟨3986256443006630264987965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5315008590675507019983953 3986256443006630264987965)
        ·
          refine ⟨1494846166127486349370487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3986256443006630264987965 1494846166127486349370487)
          ·
            refine ⟨2242269249191229524055731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494846166127486349370487 2242269249191229524055731)
            ·
              refine ⟨3363403873786844286083597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2242269249191229524055731 3363403873786844286083597)
              ·
                refine ⟨1261276452670066607281349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3363403873786844286083597 1261276452670066607281349)
                ·
                  refine ⟨236489334875637488865253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1261276452670066607281349 236489334875637488865253)
                  ·
                    rfl

theorem cell21_1036263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 4].length) (baseStart_1036263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036263 prefixEnd_1036263 := by exact prefixLift 1036263
  have htrace : WordTrace (prefixWord ++ tailWord_1036263) baseStart_1036263 baseEnd_1036263 := by
    simpa [prefixWord, tailWord_1036263, baseEnd_1036263] using wordTrace_append hprefix tailTrace_1036263
  have hstable : (prefixWord ++ tailWord_1036263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036263).length < 2 ^ (prefixWord ++ tailWord_1036263).sum := by decide
  have hdescent : baseEnd_1036263 < baseStart_1036263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036322 : List Nat := [3, 3, 1, 1, 1, 2, 1, 5, 4]
def baseStart_1036322 : Nat := 118140960795 + 1036322 * 2 ^ 59
def prefixEnd_1036322 : Nat := 4983230072969 + 3 ^ 40 * 1036322 * 2
def baseEnd_1036322 : Nat := 236502799479466497381799

theorem tailTrace_1036322 : CollatzResearch.WordTrace tailWord_1036322 prefixEnd_1036322 236502799479466497381799 := by
  unfold tailWord_1036322
  simp only [CollatzResearch.WordTrace]
  refine ⟨9449442137897464637959805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25198512367726572367892813 9449442137897464637959805)
  ·
    refine ⟨3543540801711549239234927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9449442137897464637959805 3543540801711549239234927)
    ·
      refine ⟨5315311202567323858852391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3543540801711549239234927 5315311202567323858852391)
      ·
        refine ⟨7972966803850985788278587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5315311202567323858852391 7972966803850985788278587)
        ·
          refine ⟨11959450205776478682417881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7972966803850985788278587 11959450205776478682417881)
          ·
            refine ⟨8969587654332359011813411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11959450205776478682417881 8969587654332359011813411)
            ·
              refine ⟨13454381481498538517720117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8969587654332359011813411 13454381481498538517720117)
              ·
                refine ⟨1261348263890487986036261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13454381481498538517720117 1261348263890487986036261)
                ·
                  refine ⟨236502799479466497381799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1261348263890487986036261 236502799479466497381799)
                  ·
                    rfl

theorem cell21_1036322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_1036322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036322 prefixEnd_1036322 := by exact prefixLift 1036322
  have htrace : WordTrace (prefixWord ++ tailWord_1036322) baseStart_1036322 baseEnd_1036322 := by
    simpa [prefixWord, tailWord_1036322, baseEnd_1036322] using wordTrace_append hprefix tailTrace_1036322
  have hstable : (prefixWord ++ tailWord_1036322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036322).length < 2 ^ (prefixWord ++ tailWord_1036322).sum := by decide
  have hdescent : baseEnd_1036322 < baseStart_1036322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036412 : List Nat := [2, 2, 2, 1, 1, 6, 7]
def baseStart_1036412 : Nat := 118140960795 + 1036412 * 2 ^ 59
def prefixEnd_1036412 : Nat := 4983230072969 + 3 ^ 40 * 1036412 * 2
def baseEnd_1036412 : Nat := 26280370967294037875735

theorem tailTrace_1036412 : CollatzResearch.WordTrace tailWord_1036412 prefixEnd_1036412 26280370967294037875735 := by
  unfold tailWord_1036412
  simp only [CollatzResearch.WordTrace]
  refine ⟨18900525560631901961307745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25200700747509202615076993 18900525560631901961307745)
  ·
    refine ⟨14175394170473926470980809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18900525560631901961307745 14175394170473926470980809)
    ·
      refine ⟨10631545627855444853235607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14175394170473926470980809 10631545627855444853235607)
      ·
        refine ⟨15947318441783167279853411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10631545627855444853235607 15947318441783167279853411)
        ·
          refine ⟨23920977662674750919780117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15947318441783167279853411 23920977662674750919780117)
          ·
            refine ⟨1121295827937878949364693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23920977662674750919780117 1121295827937878949364693)
            ·
              refine ⟨26280370967294037875735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1121295827937878949364693 26280370967294037875735)
              ·
                rfl

theorem cell21_1036412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 7].length) (baseStart_1036412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036412 prefixEnd_1036412 := by exact prefixLift 1036412
  have htrace : WordTrace (prefixWord ++ tailWord_1036412) baseStart_1036412 baseEnd_1036412 := by
    simpa [prefixWord, tailWord_1036412, baseEnd_1036412] using wordTrace_append hprefix tailTrace_1036412
  have hstable : (prefixWord ++ tailWord_1036412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036412).length < 2 ^ (prefixWord ++ tailWord_1036412).sum := by decide
  have hdescent : baseEnd_1036412 < baseStart_1036412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036471 : List Nat := [1, 1, 3, 1, 4, 11]
def baseStart_1036471 : Nat := 118140960795 + 1036471 * 2 ^ 59
def prefixEnd_1036471 : Nat := 4983230072969 + 3 ^ 40 * 1036471 * 2
def baseEnd_1036471 : Nat := 8760622344795383311043

theorem tailTrace_1036471 : CollatzResearch.WordTrace tailWord_1036471 prefixEnd_1036471 8760622344795383311043 := by
  unfold tailWord_1036471
  simp only [CollatzResearch.WordTrace]
  refine ⟨37803203028050056999013267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25202135352033371332675511 37803203028050056999013267)
  ·
    refine ⟨56704804542075085498519901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37803203028050056999013267 56704804542075085498519901)
    ·
      refine ⟨21264301703278157061944963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56704804542075085498519901 21264301703278157061944963)
      ·
        refine ⟨31896452554917235592917445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21264301703278157061944963 31896452554917235592917445)
        ·
          refine ⟨5980584854046981673672021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31896452554917235592917445 5980584854046981673672021)
          ·
            refine ⟨8760622344795383311043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5980584854046981673672021 8760622344795383311043)
            ·
              rfl

theorem cell21_1036471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 11].length) (baseStart_1036471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036471 prefixEnd_1036471 := by exact prefixLift 1036471
  have htrace : WordTrace (prefixWord ++ tailWord_1036471) baseStart_1036471 baseEnd_1036471 := by
    simpa [prefixWord, tailWord_1036471, baseEnd_1036471] using wordTrace_append hprefix tailTrace_1036471
  have hstable : (prefixWord ++ tailWord_1036471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036471).length < 2 ^ (prefixWord ++ tailWord_1036471).sum := by decide
  have hdescent : baseEnd_1036471 < baseStart_1036471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036547 : List Nat := [1, 1, 1, 3, 2, 3, 2, 8]
def baseStart_1036547 : Nat := 118140960795 + 1036547 * 2 ^ 59
def prefixEnd_1036547 : Nat := 4983230072969 + 3 ^ 40 * 1036547 * 2
def baseEnd_1036547 : Nat := 78851382514972035377113

theorem tailTrace_1036547 : CollatzResearch.WordTrace tailWord_1036547 prefixEnd_1036547 78851382514972035377113 := by
  unfold tailWord_1036547
  simp only [CollatzResearch.WordTrace]
  refine ⟨37805974975774721978779895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25203983317183147985853263 37805974975774721978779895)
  ·
    refine ⟨56708962463662082968169843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37805974975774721978779895 56708962463662082968169843)
    ·
      refine ⟨85063443695493124452254765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56708962463662082968169843 85063443695493124452254765)
      ·
        refine ⟨31898791385809921669595537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85063443695493124452254765 31898791385809921669595537)
        ·
          refine ⟨23924093539357441252196653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31898791385809921669595537 23924093539357441252196653)
          ·
            refine ⟨8971535077259040469573745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23924093539357441252196653 8971535077259040469573745)
            ·
              refine ⟨6728651307944280352180309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8971535077259040469573745 6728651307944280352180309)
              ·
                refine ⟨78851382514972035377113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6728651307944280352180309 78851382514972035377113)
                ·
                  rfl

theorem cell21_1036547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 8].length) (baseStart_1036547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036547 prefixEnd_1036547 := by exact prefixLift 1036547
  have htrace : WordTrace (prefixWord ++ tailWord_1036547) baseStart_1036547 baseEnd_1036547 := by
    simpa [prefixWord, tailWord_1036547, baseEnd_1036547] using wordTrace_append hprefix tailTrace_1036547
  have hstable : (prefixWord ++ tailWord_1036547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036547).length < 2 ^ (prefixWord ++ tailWord_1036547).sum := by decide
  have hdescent : baseEnd_1036547 < baseStart_1036547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036570 : List Nat := [3, 1, 1, 3, 5, 1, 1, 3, 3]
def baseStart_1036570 : Nat := 118140960795 + 1036570 * 2 ^ 59
def prefixEnd_1036570 : Nat := 4983230072969 + 3 ^ 40 * 1036570 * 2
def baseEnd_1036570 : Nat := 236559396458273177247959

theorem tailTrace_1036570 : CollatzResearch.WordTrace tailWord_1036570 prefixEnd_1036570 236559396458273177247959 := by
  unfold tailWord_1036570
  simp only [CollatzResearch.WordTrace]
  refine ⟨9451703463672849226716791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25204542569794264604578109 9451703463672849226716791)
  ·
    refine ⟨14177555195509273840075187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9451703463672849226716791 14177555195509273840075187)
    ·
      refine ⟨21266332793263910760112781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14177555195509273840075187 21266332793263910760112781)
      ·
        refine ⟨7974874797473966535042293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21266332793263910760112781 7974874797473966535042293)
        ·
          refine ⟨747644512263184362660215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7974874797473966535042293 747644512263184362660215)
          ·
            refine ⟨1121466768394776543990323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747644512263184362660215 1121466768394776543990323)
            ·
              refine ⟨1682200152592164815985485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121466768394776543990323 1682200152592164815985485)
              ·
                refine ⟨630825057222061805994557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1682200152592164815985485 630825057222061805994557)
                ·
                  refine ⟨236559396458273177247959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 630825057222061805994557 236559396458273177247959)
                  ·
                    rfl

theorem cell21_1036570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_1036570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036570 prefixEnd_1036570 := by exact prefixLift 1036570
  have htrace : WordTrace (prefixWord ++ tailWord_1036570) baseStart_1036570 baseEnd_1036570 := by
    simpa [prefixWord, tailWord_1036570, baseEnd_1036570] using wordTrace_append hprefix tailTrace_1036570
  have hstable : (prefixWord ++ tailWord_1036570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036570).length < 2 ^ (prefixWord ++ tailWord_1036570).sum := by decide
  have hdescent : baseEnd_1036570 < baseStart_1036570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036581 : List Nat := [1, 3, 1, 2, 6, 1, 7]
def baseStart_1036581 : Nat := 118140960795 + 1036581 * 2 ^ 59
def prefixEnd_1036581 : Nat := 4983230072969 + 3 ^ 40 * 1036581 * 2
def baseEnd_1036581 : Nat := 26284656312015511396067

theorem tailTrace_1036581 : CollatzResearch.WordTrace tailWord_1036581 prefixEnd_1036581 26284656312015511396067 := by
  unfold tailWord_1036581
  simp only [CollatzResearch.WordTrace]
  refine ⟨37807215057651545785517597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25204810038434363857011731 37807215057651545785517597)
  ·
    refine ⟨14177705646619329669569099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37807215057651545785517597 14177705646619329669569099)
    ·
      refine ⟨21266558469928994504353649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14177705646619329669569099 21266558469928994504353649)
      ·
        refine ⟨15949918852446745878265237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21266558469928994504353649 15949918852446745878265237)
        ·
          refine ⟨747652446208441213043683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15949918852446745878265237 747652446208441213043683)
          ·
            refine ⟨1121478669312661819565525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747652446208441213043683 1121478669312661819565525)
            ·
              refine ⟨26284656312015511396067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1121478669312661819565525 26284656312015511396067)
              ·
                rfl

theorem cell21_1036581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 7].length) (baseStart_1036581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036581 prefixEnd_1036581 := by exact prefixLift 1036581
  have htrace : WordTrace (prefixWord ++ tailWord_1036581) baseStart_1036581 baseEnd_1036581 := by
    simpa [prefixWord, tailWord_1036581, baseEnd_1036581] using wordTrace_append hprefix tailTrace_1036581
  have hstable : (prefixWord ++ tailWord_1036581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036581).length < 2 ^ (prefixWord ++ tailWord_1036581).sum := by decide
  have hdescent : baseEnd_1036581 < baseStart_1036581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036638 : List Nat := [4, 4, 2, 1, 2, 1, 2, 2, 3]
def baseStart_1036638 : Nat := 118140960795 + 1036638 * 2 ^ 59
def prefixEnd_1036638 : Nat := 4983230072969 + 3 ^ 40 * 1036638 * 2
def baseEnd_1036638 : Nat := 236574914984720170114487

theorem tailTrace_1036638 : CollatzResearch.WordTrace tailWord_1036638 prefixEnd_1036638 236574914984720170114487 := by
  unfold tailWord_1036638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4726161752305630565042821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25206196012296696346895045 4726161752305630565042821)
  ·
    refine ⟨886155328557305730945529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4726161752305630565042821 886155328557305730945529)
    ·
      refine ⟨664616496417979298209147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 886155328557305730945529 664616496417979298209147)
      ·
        refine ⟨996924744626968947313721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664616496417979298209147 996924744626968947313721)
        ·
          refine ⟨747693558470226710485291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 996924744626968947313721 747693558470226710485291)
          ·
            refine ⟨1121540337705340065727937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747693558470226710485291 1121540337705340065727937)
            ·
              refine ⟨841155253279005049295953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1121540337705340065727937 841155253279005049295953)
              ·
                refine ⟨630866439959253786971965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 841155253279005049295953 630866439959253786971965)
                ·
                  refine ⟨236574914984720170114487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 630866439959253786971965 236574914984720170114487)
                  ·
                    rfl

theorem cell21_1036638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_1036638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036638 prefixEnd_1036638 := by exact prefixLift 1036638
  have htrace : WordTrace (prefixWord ++ tailWord_1036638) baseStart_1036638 baseEnd_1036638 := by
    simpa [prefixWord, tailWord_1036638, baseEnd_1036638] using wordTrace_append hprefix tailTrace_1036638
  have hstable : (prefixWord ++ tailWord_1036638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036638).length < 2 ^ (prefixWord ++ tailWord_1036638).sum := by decide
  have hdescent : baseEnd_1036638 < baseStart_1036638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036640 : List Nat := [2, 1, 1, 3, 6, 8]
def baseStart_1036640 : Nat := 118140960795 + 1036640 * 2 ^ 59
def prefixEnd_1036640 : Nat := 4983230072969 + 3 ^ 40 * 1036640 * 2
def baseEnd_1036640 : Nat := 8762050793035874484487

theorem tailTrace_1036640 : CollatzResearch.WordTrace tailWord_1036640 prefixEnd_1036640 8762050793035874484487 := by
  unfold tailWord_1036640
  simp only [CollatzResearch.WordTrace]
  refine ⟨18904683482218899430957687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25206244642958532574610249 18904683482218899430957687)
  ·
    refine ⟨28357025223328349146436531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18904683482218899430957687 28357025223328349146436531)
    ·
      refine ⟨42535537834992523719654797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28357025223328349146436531 42535537834992523719654797)
      ·
        refine ⟨15950826688122196394870549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42535537834992523719654797 15950826688122196394870549)
        ·
          refine ⟨747695001005727956009557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15950826688122196394870549 747695001005727956009557)
          ·
            refine ⟨8762050793035874484487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 747695001005727956009557 8762050793035874484487)
            ·
              rfl

theorem cell21_1036640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 8].length) (baseStart_1036640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036640 prefixEnd_1036640 := by exact prefixLift 1036640
  have htrace : WordTrace (prefixWord ++ tailWord_1036640) baseStart_1036640 baseEnd_1036640 := by
    simpa [prefixWord, tailWord_1036640, baseEnd_1036640] using wordTrace_append hprefix tailTrace_1036640
  have hstable : (prefixWord ++ tailWord_1036640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036640).length < 2 ^ (prefixWord ++ tailWord_1036640).sum := by decide
  have hdescent : baseEnd_1036640 < baseStart_1036640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036694 : List Nat := [5, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1036694 : Nat := 118140960795 + 1036694 * 2 ^ 59
def prefixEnd_1036694 : Nat := 4983230072969 + 3 ^ 40 * 1036694 * 2
def baseEnd_1036694 : Nat := 236587694947676517181039

theorem tailTrace_1036694 : CollatzResearch.WordTrace tailWord_1036694 prefixEnd_1036694 236587694947676517181039 := by
  unfold tailWord_1036694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2363208531640135380273821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25207557670828110722920757 2363208531640135380273821)
  ·
    refine ⟨886203199365050767602683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2363208531640135380273821 886203199365050767602683)
    ·
      refine ⟨1329304799047576151404025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 886203199365050767602683 1329304799047576151404025)
      ·
        refine ⟨996978599285682113553019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1329304799047576151404025 996978599285682113553019)
        ·
          refine ⟨1495467898928523170329529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996978599285682113553019 1495467898928523170329529)
          ·
            refine ⟨1121600924196392377747147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1495467898928523170329529 1121600924196392377747147)
            ·
              refine ⟨1682401386294588566620721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121600924196392377747147 1682401386294588566620721)
              ·
                refine ⟨1261801039720941424965541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1682401386294588566620721 1261801039720941424965541)
                ·
                  refine ⟨236587694947676517181039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1261801039720941424965541 236587694947676517181039)
                  ·
                    rfl

theorem cell21_1036694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1036694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036694 prefixEnd_1036694 := by exact prefixLift 1036694
  have htrace : WordTrace (prefixWord ++ tailWord_1036694) baseStart_1036694 baseEnd_1036694 := by
    simpa [prefixWord, tailWord_1036694, baseEnd_1036694] using wordTrace_append hprefix tailTrace_1036694
  have hstable : (prefixWord ++ tailWord_1036694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036694).length < 2 ^ (prefixWord ++ tailWord_1036694).sum := by decide
  have hdescent : baseEnd_1036694 < baseStart_1036694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036733 : List Nat := [1, 4, 1, 2, 2, 4, 2, 5]
def baseStart_1036733 : Nat := 118140960795 + 1036733 * 2 ^ 59
def prefixEnd_1036733 : Nat := 4983230072969 + 3 ^ 40 * 1036733 * 2
def baseEnd_1036733 : Nat := 78865531759673705343653

theorem tailTrace_1036733 : CollatzResearch.WordTrace tailWord_1036733 prefixEnd_1036733 78865531759673705343653 := by
  unfold tailWord_1036733
  simp only [CollatzResearch.WordTrace]
  refine ⟨37812758953100875745050853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25208505968733917163367235 37812758953100875745050853)
  ·
    refine ⟨7089892303706414202197035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37812758953100875745050853 7089892303706414202197035)
    ·
      refine ⟨10634838455559621303295553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7089892303706414202197035 10634838455559621303295553)
      ·
        refine ⟨7976128841669715977471665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10634838455559621303295553 7976128841669715977471665)
        ·
          refine ⟨5982096631252286983103749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7976128841669715977471665 5982096631252286983103749)
          ·
            refine ⟨1121643118359803809331953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5982096631252286983103749 1121643118359803809331953)
            ·
              refine ⟨841232338769852856998965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1121643118359803809331953 841232338769852856998965)
              ·
                refine ⟨78865531759673705343653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 841232338769852856998965 78865531759673705343653)
                ·
                  rfl

theorem cell21_1036733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 5].length) (baseStart_1036733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036733 prefixEnd_1036733 := by exact prefixLift 1036733
  have htrace : WordTrace (prefixWord ++ tailWord_1036733) baseStart_1036733 baseEnd_1036733 := by
    simpa [prefixWord, tailWord_1036733, baseEnd_1036733] using wordTrace_append hprefix tailTrace_1036733
  have hstable : (prefixWord ++ tailWord_1036733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036733).length < 2 ^ (prefixWord ++ tailWord_1036733).sum := by decide
  have hdescent : baseEnd_1036733 < baseStart_1036733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036761 : List Nat := [1, 2, 1, 2, 4, 1, 2, 4, 4]
def baseStart_1036761 : Nat := 118140960795 + 1036761 * 2 ^ 59
def prefixEnd_1036761 : Nat := 4983230072969 + 3 ^ 40 * 1036761 * 2
def baseEnd_1036761 : Nat := 236602985260499289564235

theorem tailTrace_1036761 : CollatzResearch.WordTrace tailWord_1036761 prefixEnd_1036761 236602985260499289564235 := by
  unfold tailWord_1036761
  simp only [CollatzResearch.WordTrace]
  refine ⟨37813780196999436527070137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25209186797999624351380091 37813780196999436527070137)
  ·
    refine ⟨28360335147749577395302603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37813780196999436527070137 28360335147749577395302603)
    ·
      refine ⟨42540502721624366092953905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28360335147749577395302603 42540502721624366092953905)
      ·
        refine ⟨31905377041218274569715429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42540502721624366092953905 31905377041218274569715429)
        ·
          refine ⟨5982258195228426481821643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31905377041218274569715429 5982258195228426481821643)
          ·
            refine ⟨8973387292842639722732465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5982258195228426481821643 8973387292842639722732465)
            ·
              refine ⟨6730040469631979792049349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8973387292842639722732465 6730040469631979792049349)
              ·
                refine ⟨1261882588055996211009253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6730040469631979792049349 1261882588055996211009253)
                ·
                  refine ⟨236602985260499289564235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1261882588055996211009253 236602985260499289564235)
                  ·
                    rfl

theorem cell21_1036761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 4].length) (baseStart_1036761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036761 prefixEnd_1036761 := by exact prefixLift 1036761
  have htrace : WordTrace (prefixWord ++ tailWord_1036761) baseStart_1036761 baseEnd_1036761 := by
    simpa [prefixWord, tailWord_1036761, baseEnd_1036761] using wordTrace_append hprefix tailTrace_1036761
  have hstable : (prefixWord ++ tailWord_1036761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036761).length < 2 ^ (prefixWord ++ tailWord_1036761).sum := by decide
  have hdescent : baseEnd_1036761 < baseStart_1036761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036770 : List Nat := [3, 3, 3, 2, 2, 1, 2, 1, 4]
def baseStart_1036770 : Nat := 118140960795 + 1036770 * 2 ^ 59
def prefixEnd_1036770 : Nat := 4983230072969 + 3 ^ 40 * 1036770 * 2
def baseEnd_1036770 : Nat := 236605039183117273914217

theorem tailTrace_1036770 : CollatzResearch.WordTrace tailWord_1036770 prefixEnd_1036770 236605039183117273914217 := by
  unfold tailWord_1036770
  simp only [CollatzResearch.WordTrace]
  refine ⟨9453527113491707766036941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25209405635977887376098509 9453527113491707766036941)
  ·
    refine ⟨3545072667559390412263853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9453527113491707766036941 3545072667559390412263853)
    ·
      refine ⟨1329402250334771404598945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3545072667559390412263853 1329402250334771404598945)
      ·
        refine ⟨997051687751078553449209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1329402250334771404598945 997051687751078553449209)
        ·
          refine ⟨747788765813308915086907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 997051687751078553449209 747788765813308915086907)
          ·
            refine ⟨1121683148719963372630361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747788765813308915086907 1121683148719963372630361)
            ·
              refine ⟨841262361539972529472771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1121683148719963372630361 841262361539972529472771)
              ·
                refine ⟨1261893542309958794209157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841262361539972529472771 1261893542309958794209157)
                ·
                  refine ⟨236605039183117273914217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1261893542309958794209157 236605039183117273914217)
                  ·
                    rfl

theorem cell21_1036770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_1036770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036770 prefixEnd_1036770 := by exact prefixLift 1036770
  have htrace : WordTrace (prefixWord ++ tailWord_1036770) baseStart_1036770 baseEnd_1036770 := by
    simpa [prefixWord, tailWord_1036770, baseEnd_1036770] using wordTrace_append hprefix tailTrace_1036770
  have hstable : (prefixWord ++ tailWord_1036770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036770).length < 2 ^ (prefixWord ++ tailWord_1036770).sum := by decide
  have hdescent : baseEnd_1036770 < baseStart_1036770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036778 : List Nat := [3, 1, 3, 1, 3, 2, 1, 3, 4]
def baseStart_1036778 : Nat := 118140960795 + 1036778 * 2 ^ 59
def prefixEnd_1036778 : Nat := 4983230072969 + 3 ^ 40 * 1036778 * 2
def baseEnd_1036778 : Nat := 236606864892111037780867

theorem tailTrace_1036778 : CollatzResearch.WordTrace tailWord_1036778 prefixEnd_1036778 236606864892111037780867 := by
  unfold tailWord_1036778
  simp only [CollatzResearch.WordTrace]
  refine ⟨9453600059484462107609747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25209600158625232286959325 9453600059484462107609747)
  ·
    refine ⟨14180400089226693161414621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9453600059484462107609747 14180400089226693161414621)
    ·
      refine ⟨5317650033460009935530483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14180400089226693161414621 5317650033460009935530483)
      ·
        refine ⟨7976475050190014903295725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5317650033460009935530483 7976475050190014903295725)
        ·
          refine ⟨2991178143821255588735897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7976475050190014903295725 2991178143821255588735897)
          ·
            refine ⟨2243383607865941691551923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2991178143821255588735897 2243383607865941691551923)
            ·
              refine ⟨3365075411798912537327885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2243383607865941691551923 3365075411798912537327885)
              ·
                refine ⟨1261903279424592201497957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3365075411798912537327885 1261903279424592201497957)
                ·
                  refine ⟨236606864892111037780867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1261903279424592201497957 236606864892111037780867)
                  ·
                    rfl

theorem cell21_1036778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_1036778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036778 prefixEnd_1036778 := by exact prefixLift 1036778
  have htrace : WordTrace (prefixWord ++ tailWord_1036778) baseStart_1036778 baseEnd_1036778 := by
    simpa [prefixWord, tailWord_1036778, baseEnd_1036778] using wordTrace_append hprefix tailTrace_1036778
  have hstable : (prefixWord ++ tailWord_1036778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036778).length < 2 ^ (prefixWord ++ tailWord_1036778).sum := by decide
  have hdescent : baseEnd_1036778 < baseStart_1036778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036837 : List Nat := [1, 3, 1, 2, 2, 1, 4, 3, 4]
def baseStart_1036837 : Nat := 118140960795 + 1036837 * 2 ^ 59
def prefixEnd_1036837 : Nat := 4983230072969 + 3 ^ 40 * 1036837 * 2
def baseEnd_1036837 : Nat := 236620329495940046297413

theorem tailTrace_1036837 : CollatzResearch.WordTrace tailWord_1036837 prefixEnd_1036837 236620329495940046297413 := by
  unfold tailWord_1036837
  simp only [CollatzResearch.WordTrace]
  refine ⟨37816552144724101506836765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25211034763149401004557843 37816552144724101506836765)
  ·
    refine ⟨14181207054271538065063787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37816552144724101506836765 14181207054271538065063787)
    ·
      refine ⟨21271810581407307097595681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14181207054271538065063787 21271810581407307097595681)
      ·
        refine ⟨15953857936055480323196761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21271810581407307097595681 15953857936055480323196761)
        ·
          refine ⟨11965393452041610242397571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15953857936055480323196761 11965393452041610242397571)
          ·
            refine ⟨17948090178062415363596357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11965393452041610242397571 17948090178062415363596357)
            ·
              refine ⟨3365266908386702880674317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17948090178062415363596357 3365266908386702880674317)
              ·
                refine ⟨1261975090645013580252869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3365266908386702880674317 1261975090645013580252869)
                ·
                  refine ⟨236620329495940046297413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1261975090645013580252869 236620329495940046297413)
                  ·
                    rfl

theorem cell21_1036837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_1036837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036837 prefixEnd_1036837 := by exact prefixLift 1036837
  have htrace : WordTrace (prefixWord ++ tailWord_1036837) baseStart_1036837 baseEnd_1036837 := by
    simpa [prefixWord, tailWord_1036837, baseEnd_1036837] using wordTrace_append hprefix tailTrace_1036837
  have hstable : (prefixWord ++ tailWord_1036837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036837).length < 2 ^ (prefixWord ++ tailWord_1036837).sum := by decide
  have hdescent : baseEnd_1036837 < baseStart_1036837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036989 : List Nat := [1, 4, 1, 2, 1, 3, 1, 4, 4]
def baseStart_1036989 : Nat := 118140960795 + 1036989 * 2 ^ 59
def prefixEnd_1036989 : Nat := 4983230072969 + 3 ^ 40 * 1036989 * 2
def baseEnd_1036989 : Nat := 236655017966821559763769

theorem tailTrace_1036989 : CollatzResearch.WordTrace tailWord_1036989 prefixEnd_1036989 236655017966821559763769 := by
  unfold tailWord_1036989
  simp only [CollatzResearch.WordTrace]
  refine ⟨37822096040173431466370021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25214730693448954310913347 37822096040173431466370021)
  ·
    refine ⟨7091643007532518399944379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37822096040173431466370021 7091643007532518399944379)
    ·
      refine ⟨10637464511298777599916569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7091643007532518399944379 10637464511298777599916569)
      ·
        refine ⟨7978098383474083199937427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10637464511298777599916569 7978098383474083199937427)
        ·
          refine ⟨11967147575211124799906141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7978098383474083199937427 11967147575211124799906141)
          ·
            refine ⟨4487680340704171799964803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11967147575211124799906141 4487680340704171799964803)
            ·
              refine ⟨6731520511056257699947205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4487680340704171799964803 6731520511056257699947205)
              ·
                refine ⟨1262160095823048318740101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6731520511056257699947205 1262160095823048318740101)
                ·
                  refine ⟨236655017966821559763769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1262160095823048318740101 236655017966821559763769)
                  ·
                    rfl

theorem cell21_1036989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_1036989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036989 prefixEnd_1036989 := by exact prefixLift 1036989
  have htrace : WordTrace (prefixWord ++ tailWord_1036989) baseStart_1036989 baseEnd_1036989 := by
    simpa [prefixWord, tailWord_1036989, baseEnd_1036989] using wordTrace_append hprefix tailTrace_1036989
  have hstable : (prefixWord ++ tailWord_1036989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036989).length < 2 ^ (prefixWord ++ tailWord_1036989).sum := by decide
  have hdescent : baseEnd_1036989 < baseStart_1036989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036992 : List Nat := [2, 1, 1, 2, 4, 2, 4, 2, 3]
def baseStart_1036992 : Nat := 118140960795 + 1036992 * 2 ^ 59
def prefixEnd_1036992 : Nat := 4983230072969 + 3 ^ 40 * 1036992 * 2
def baseEnd_1036992 : Nat := 236655702607694221213763

theorem tailTrace_1036992 : CollatzResearch.WordTrace tailWord_1036992 prefixEnd_1036992 236655702607694221213763 := by
  unfold tailWord_1036992
  simp only [CollatzResearch.WordTrace]
  refine ⟨18911102729581281489364615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25214803639441708652486153 18911102729581281489364615)
  ·
    refine ⟨28366654094371922234046923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18911102729581281489364615 28366654094371922234046923)
    ·
      refine ⟨42549981141557883351070385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28366654094371922234046923 42549981141557883351070385)
      ·
        refine ⟨31912485856168412513302789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42549981141557883351070385 31912485856168412513302789)
        ·
          refine ⟨5983591098031577346244273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31912485856168412513302789 5983591098031577346244273)
          ·
            refine ⟨4487693323523683009683205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5983591098031577346244273 4487693323523683009683205)
            ·
              refine ⟨841442498160690564315601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4487693323523683009683205 841442498160690564315601)
              ·
                refine ⟨631081873620517923236701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 841442498160690564315601 631081873620517923236701)
                ·
                  refine ⟨236655702607694221213763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 631081873620517923236701 236655702607694221213763)
                  ·
                    rfl

theorem cell21_1036992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 3].length) (baseStart_1036992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1036992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1036992 prefixEnd_1036992 := by exact prefixLift 1036992
  have htrace : WordTrace (prefixWord ++ tailWord_1036992) baseStart_1036992 baseEnd_1036992 := by
    simpa [prefixWord, tailWord_1036992, baseEnd_1036992] using wordTrace_append hprefix tailTrace_1036992
  have hstable : (prefixWord ++ tailWord_1036992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036992).length < 2 ^ (prefixWord ++ tailWord_1036992).sum := by decide
  have hdescent : baseEnd_1036992 < baseStart_1036992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037048 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 6]
def baseStart_1037048 : Nat := 118140960795 + 1037048 * 2 ^ 59
def prefixEnd_1037048 : Nat := 4983230072969 + 3 ^ 40 * 1037048 * 2
def baseEnd_1037048 : Nat := 236668482570650568280315

theorem tailTrace_1037048 : CollatzResearch.WordTrace tailWord_1037048 prefixEnd_1037048 236668482570650568280315 := by
  unfold tailWord_1037048
  simp only [CollatzResearch.WordTrace]
  refine ⟨18912123973479842271383899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25216165297973123028511865 18912123973479842271383899)
  ·
    refine ⟨28368185960219763407075849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18912123973479842271383899 28368185960219763407075849)
    ·
      refine ⟨21276139470164822555306887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28368185960219763407075849 21276139470164822555306887)
      ·
        refine ⟨31914209205247233832960331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21276139470164822555306887 31914209205247233832960331)
        ·
          refine ⟨47871313807870850749440497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31914209205247233832960331 47871313807870850749440497)
          ·
            refine ⟨35903485355903138062080373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47871313807870850749440497 35903485355903138062080373)
            ·
              refine ⟨3365951752115919193320035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35903485355903138062080373 3365951752115919193320035)
              ·
                refine ⟨5048927628173878789980053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3365951752115919193320035 5048927628173878789980053)
                ·
                  refine ⟨236668482570650568280315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5048927628173878789980053 236668482570650568280315)
                  ·
                    rfl

theorem cell21_1037048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_1037048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1037048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1037048 prefixEnd_1037048 := by exact prefixLift 1037048
  have htrace : WordTrace (prefixWord ++ tailWord_1037048) baseStart_1037048 baseEnd_1037048 := by
    simpa [prefixWord, tailWord_1037048, baseEnd_1037048] using wordTrace_append hprefix tailTrace_1037048
  have hstable : (prefixWord ++ tailWord_1037048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037048).length < 2 ^ (prefixWord ++ tailWord_1037048).sum := by decide
  have hdescent : baseEnd_1037048 < baseStart_1037048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037217 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 6]
def baseStart_1037217 : Nat := 118140960795 + 1037217 * 2 ^ 59
def prefixEnd_1037217 : Nat := 4983230072969 + 3 ^ 40 * 1037217 * 2
def baseEnd_1037217 : Nat := 236707050673143829963303

theorem tailTrace_1037217 : CollatzResearch.WordTrace tailWord_1037217 prefixEnd_1037217 236707050673143829963303 := by
  unfold tailWord_1037217
  simp only [CollatzResearch.WordTrace]
  refine ⟨37830411883347426405669905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25220274588898284270446603 37830411883347426405669905)
  ·
    refine ⟨28372808912510569804252429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37830411883347426405669905 28372808912510569804252429)
    ·
      refine ⟨10639803342191463676594661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28372808912510569804252429 10639803342191463676594661)
      ·
        refine ⟨1994963126660899439361499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10639803342191463676594661 1994963126660899439361499)
        ·
          refine ⟨2992444689991349159042249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1994963126660899439361499 2992444689991349159042249)
          ·
            refine ⟨2244333517493511869281687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2992444689991349159042249 2244333517493511869281687)
            ·
              refine ⟨3366500276240267803922531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2244333517493511869281687 3366500276240267803922531)
              ·
                refine ⟨5049750414360401705883797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3366500276240267803922531 5049750414360401705883797)
                ·
                  refine ⟨236707050673143829963303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5049750414360401705883797 236707050673143829963303)
                  ·
                    rfl

theorem cell21_1037217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_1037217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1037217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1037217 prefixEnd_1037217 := by exact prefixLift 1037217
  have htrace : WordTrace (prefixWord ++ tailWord_1037217) baseStart_1037217 baseEnd_1037217 := by
    simpa [prefixWord, tailWord_1037217, baseEnd_1037217] using wordTrace_append hprefix tailTrace_1037217
  have hstable : (prefixWord ++ tailWord_1037217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037217).length < 2 ^ (prefixWord ++ tailWord_1037217).sum := by decide
  have hdescent : baseEnd_1037217 < baseStart_1037217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037248 : List Nat := [2, 1, 1, 2, 3, 5, 2, 5]
def baseStart_1037248 : Nat := 118140960795 + 1037248 * 2 ^ 59
def prefixEnd_1037248 : Nat := 4983230072969 + 3 ^ 40 * 1037248 * 2
def baseEnd_1037248 : Nat := 78904708431831554982191

theorem tailTrace_1037248 : CollatzResearch.WordTrace tailWord_1037248 prefixEnd_1037248 78904708431831554982191 := by
  unfold tailWord_1037248
  simp only [CollatzResearch.WordTrace]
  refine ⟨18915771273117559350024199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25221028364156745800032265 18915771273117559350024199)
  ·
    refine ⟨28373656909676339025036299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18915771273117559350024199 28373656909676339025036299)
    ·
      refine ⟨42560485364514508537554449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28373656909676339025036299 42560485364514508537554449)
      ·
        refine ⟨31920364023385881403165837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42560485364514508537554449 31920364023385881403165837)
        ·
          refine ⟨11970136508769705526187189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31920364023385881403165837 11970136508769705526187189)
          ·
            refine ⟨1122200297697159893080049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11970136508769705526187189 1122200297697159893080049)
            ·
              refine ⟨841650223272869919810037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1122200297697159893080049 841650223272869919810037)
              ·
                refine ⟨78904708431831554982191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 841650223272869919810037 78904708431831554982191)
                ·
                  rfl

theorem cell21_1037248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 5].length) (baseStart_1037248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1037248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1037248 prefixEnd_1037248 := by exact prefixLift 1037248
  have htrace : WordTrace (prefixWord ++ tailWord_1037248) baseStart_1037248 baseEnd_1037248 := by
    simpa [prefixWord, tailWord_1037248, baseEnd_1037248] using wordTrace_append hprefix tailTrace_1037248
  have hstable : (prefixWord ++ tailWord_1037248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037248).length < 2 ^ (prefixWord ++ tailWord_1037248).sum := by decide
  have hdescent : baseEnd_1037248 < baseStart_1037248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037279 : List Nat := [1, 1, 2, 3, 5, 2, 1, 1, 5]
def baseStart_1037279 : Nat := 118140960795 + 1037279 * 2 ^ 59
def prefixEnd_1037279 : Nat := 4983230072969 + 3 ^ 40 * 1037279 * 2
def baseEnd_1037279 : Nat := 236721199917845499929843

theorem tailTrace_1037279 : CollatzResearch.WordTrace tailWord_1037279 prefixEnd_1037279 236721199917845499929843 := by
  unfold tailWord_1037279
  simp only [CollatzResearch.WordTrace]
  refine ⟨37832673209122810994426891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25221782139415207329617927 37832673209122810994426891)
  ·
    refine ⟨56749009813684216491640337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37832673209122810994426891 56749009813684216491640337)
    ·
      refine ⟨42561757360263162368730253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56749009813684216491640337 42561757360263162368730253)
      ·
        refine ⟨15960659010098685888273845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42561757360263162368730253 15960659010098685888273845)
        ·
          refine ⟨1496311782196751802025673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15960659010098685888273845 1496311782196751802025673)
          ·
            refine ⟨1122233836647563851519255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1496311782196751802025673 1122233836647563851519255)
            ·
              refine ⟨1683350754971345777278883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122233836647563851519255 1683350754971345777278883)
              ·
                refine ⟨2525026132457018665918325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1683350754971345777278883 2525026132457018665918325)
                ·
                  refine ⟨236721199917845499929843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2525026132457018665918325 236721199917845499929843)
                  ·
                    rfl

theorem cell21_1037279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 5].length) (baseStart_1037279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1037279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1037279 prefixEnd_1037279 := by exact prefixLift 1037279
  have htrace : WordTrace (prefixWord ++ tailWord_1037279) baseStart_1037279 baseEnd_1037279 := by
    simpa [prefixWord, tailWord_1037279, baseEnd_1037279] using wordTrace_append hprefix tailTrace_1037279
  have hstable : (prefixWord ++ tailWord_1037279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037279).length < 2 ^ (prefixWord ++ tailWord_1037279).sum := by decide
  have hdescent : baseEnd_1037279 < baseStart_1037279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037330 : List Nat := [3, 2, 5, 1, 1, 1, 1, 4, 3]
def baseStart_1037330 : Nat := 118140960795 + 1037330 * 2 ^ 59
def prefixEnd_1037330 : Nat := 4983230072969 + 3 ^ 40 * 1037330 * 2
def baseEnd_1037330 : Nat := 236732838812680744579739

theorem tailTrace_1037330 : CollatzResearch.WordTrace tailWord_1037330 prefixEnd_1037330 236732838812680744579739 := by
  unfold tailWord_1037330
  simp only [CollatzResearch.WordTrace]
  refine ⟨9458633332984511676133361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25223022221292031136355629 9458633332984511676133361)
  ·
    refine ⟨7093974999738383757100021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9458633332984511676133361 7093974999738383757100021)
    ·
      refine ⟨665060156225473477228127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7093974999738383757100021 665060156225473477228127)
      ·
        refine ⟨997590234338210215842191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665060156225473477228127 997590234338210215842191)
        ·
          refine ⟨1496385351507315323763287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997590234338210215842191 1496385351507315323763287)
          ·
            refine ⟨2244578027260972985644931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1496385351507315323763287 2244578027260972985644931)
            ·
              refine ⟨3366867040891459478467397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2244578027260972985644931 3366867040891459478467397)
              ·
                refine ⟨631287570167148652212637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3366867040891459478467397 631287570167148652212637)
                ·
                  refine ⟨236732838812680744579739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 631287570167148652212637 236732838812680744579739)
                  ·
                    rfl

theorem cell21_1037330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_1037330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1037330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1037330 prefixEnd_1037330 := by exact prefixLift 1037330
  have htrace : WordTrace (prefixWord ++ tailWord_1037330) baseStart_1037330 baseEnd_1037330 := by
    simpa [prefixWord, tailWord_1037330, baseEnd_1037330] using wordTrace_append hprefix tailTrace_1037330
  have hstable : (prefixWord ++ tailWord_1037330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037330).length < 2 ^ (prefixWord ++ tailWord_1037330).sum := by decide
  have hdescent : baseEnd_1037330 < baseStart_1037330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037341 : List Nat := [1, 4, 2, 2, 4, 1, 1, 6]
def baseStart_1037341 : Nat := 118140960795 + 1037341 * 2 ^ 59
def prefixEnd_1037341 : Nat := 4983230072969 + 3 ^ 40 * 1037341 * 2
def baseEnd_1037341 : Nat := 78911783054182389965461

theorem tailTrace_1037341 : CollatzResearch.WordTrace tailWord_1037341 prefixEnd_1037341 78911783054182389965461 := by
  unfold tailWord_1037341
  simp only [CollatzResearch.WordTrace]
  refine ⟨37834934534898195583183877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25223289689932130388789251 37834934534898195583183877)
  ·
    refine ⟨7094050225293411671846977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37834934534898195583183877 7094050225293411671846977)
    ·
      refine ⟨5320537668970058753885233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7094050225293411671846977 5320537668970058753885233)
      ·
        refine ⟨3990403251727544065413925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5320537668970058753885233 3990403251727544065413925)
        ·
          refine ⟨748200609698914512265111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3990403251727544065413925 748200609698914512265111)
          ·
            refine ⟨1122300914548371768397667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748200609698914512265111 1122300914548371768397667)
            ·
              refine ⟨1683451371822557652596501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122300914548371768397667 1683451371822557652596501)
              ·
                refine ⟨78911783054182389965461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1683451371822557652596501 78911783054182389965461)
                ·
                  rfl

theorem cell21_1037341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 6].length) (baseStart_1037341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1037341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1037341 prefixEnd_1037341 := by exact prefixLift 1037341
  have htrace : WordTrace (prefixWord ++ tailWord_1037341) baseStart_1037341 baseEnd_1037341 := by
    simpa [prefixWord, tailWord_1037341, baseEnd_1037341] using wordTrace_append hprefix tailTrace_1037341
  have hstable : (prefixWord ++ tailWord_1037341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037341).length < 2 ^ (prefixWord ++ tailWord_1037341).sum := by decide
  have hdescent : baseEnd_1037341 < baseStart_1037341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037448 : List Nat := [2, 1, 3, 4, 3, 1, 1, 1, 5]
def baseStart_1037448 : Nat := 118140960795 + 1037448 * 2 ^ 59
def prefixEnd_1037448 : Nat := 4983230072969 + 3 ^ 40 * 1037448 * 2
def baseEnd_1037448 : Nat := 236759768020338761612831

theorem tailTrace_1037448 : CollatzResearch.WordTrace tailWord_1037448 prefixEnd_1037448 236759768020338761612831 := by
  unfold tailWord_1037448
  simp only [CollatzResearch.WordTrace]
  refine ⟨18919418572755276428664499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25225891430340368571552665 18919418572755276428664499)
  ·
    refine ⟨28379127859132914642996749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18919418572755276428664499 28379127859132914642996749)
    ·
      refine ⟨10642172947174842991123781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28379127859132914642996749 10642172947174842991123781)
      ·
        refine ⟨1995407427595283060835709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10642172947174842991123781 1995407427595283060835709)
        ·
          refine ⟨748277785348231147813391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1995407427595283060835709 748277785348231147813391)
          ·
            refine ⟨1122416678022346721720087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748277785348231147813391 1122416678022346721720087)
            ·
              refine ⟨1683625017033520082580131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122416678022346721720087 1683625017033520082580131)
              ·
                refine ⟨2525437525550280123870197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1683625017033520082580131 2525437525550280123870197)
                ·
                  refine ⟨236759768020338761612831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2525437525550280123870197 236759768020338761612831)
                  ·
                    rfl

theorem cell21_1037448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 5].length) (baseStart_1037448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1037448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1037448 prefixEnd_1037448 := by exact prefixLift 1037448
  have htrace : WordTrace (prefixWord ++ tailWord_1037448) baseStart_1037448 baseEnd_1037448 := by
    simpa [prefixWord, tailWord_1037448, baseEnd_1037448] using wordTrace_append hprefix tailTrace_1037448
  have hstable : (prefixWord ++ tailWord_1037448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037448).length < 2 ^ (prefixWord ++ tailWord_1037448).sum := by decide
  have hdescent : baseEnd_1037448 < baseStart_1037448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037473 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 7]
def baseStart_1037473 : Nat := 118140960795 + 1037473 * 2 ^ 59
def prefixEnd_1037473 : Nat := 4983230072969 + 3 ^ 40 * 1037473 * 2
def baseEnd_1037473 : Nat := 236765473360944273696113

theorem tailTrace_1037473 : CollatzResearch.WordTrace tailWord_1037473 prefixEnd_1037473 236765473360944273696113 := by
  unfold tailWord_1037473
  simp only [CollatzResearch.WordTrace]
  refine ⟨37839748970419982126989073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25226499313613321417992715 37839748970419982126989073)
  ·
    refine ⟨28379811727814986595241805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37839748970419982126989073 28379811727814986595241805)
    ·
      refine ⟨10642429397930619973215677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28379811727814986595241805 10642429397930619973215677)
      ·
        refine ⟨3990911024223982489955879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10642429397930619973215677 3990911024223982489955879)
        ·
          refine ⟨5986366536335973734933819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3990911024223982489955879 5986366536335973734933819)
          ·
            refine ⟨8979549804503960602400729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5986366536335973734933819 8979549804503960602400729)
            ·
              refine ⟨6734662353377970451800547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8979549804503960602400729 6734662353377970451800547)
              ·
                refine ⟨10101993530066955677700821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6734662353377970451800547 10101993530066955677700821)
                ·
                  refine ⟨236765473360944273696113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10101993530066955677700821 236765473360944273696113)
                  ·
                    rfl

theorem cell21_1037473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_1037473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1037473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1037473 prefixEnd_1037473 := by exact prefixLift 1037473
  have htrace : WordTrace (prefixWord ++ tailWord_1037473) baseStart_1037473 baseEnd_1037473 := by
    simpa [prefixWord, tailWord_1037473, baseEnd_1037473] using wordTrace_append hprefix tailTrace_1037473
  have hstable : (prefixWord ++ tailWord_1037473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037473).length < 2 ^ (prefixWord ++ tailWord_1037473).sum := by decide
  have hdescent : baseEnd_1037473 < baseStart_1037473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037487 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 8]
def baseStart_1037487 : Nat := 118140960795 + 1037487 * 2 ^ 59
def prefixEnd_1037487 : Nat := 4983230072969 + 3 ^ 40 * 1037487 * 2
def baseEnd_1037487 : Nat := 236768668351683360462751

theorem tailTrace_1037487 : CollatzResearch.WordTrace tailWord_1037487 prefixEnd_1037487 236768668351683360462751 := by
  unfold tailWord_1037487
  simp only [CollatzResearch.WordTrace]
  refine ⟨37840259592369262517998715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25226839728246175011999143 37840259592369262517998715)
  ·
    refine ⟨56760389388553893776998073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37840259592369262517998715 56760389388553893776998073)
    ·
      refine ⟨42570292041415420332748555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56760389388553893776998073 42570292041415420332748555)
      ·
        refine ⟨63855438062123130499122833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42570292041415420332748555 63855438062123130499122833)
        ·
          refine ⟨47891578546592347874342125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63855438062123130499122833 47891578546592347874342125)
          ·
            refine ⟨17959341954972130452878297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47891578546592347874342125 17959341954972130452878297)
            ·
              refine ⟨13469506466229097839658723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17959341954972130452878297 13469506466229097839658723)
              ·
                refine ⟨20204259699343646759488085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13469506466229097839658723 20204259699343646759488085)
                ·
                  refine ⟨236768668351683360462751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20204259699343646759488085 236768668351683360462751)
                  ·
                    rfl

theorem cell21_1037487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 8].length) (baseStart_1037487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1037487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1037487 prefixEnd_1037487 := by exact prefixLift 1037487
  have htrace : WordTrace (prefixWord ++ tailWord_1037487) baseStart_1037487 baseEnd_1037487 := by
    simpa [prefixWord, tailWord_1037487, baseEnd_1037487] using wordTrace_append hprefix tailTrace_1037487
  have hstable : (prefixWord ++ tailWord_1037487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037487).length < 2 ^ (prefixWord ++ tailWord_1037487).sum := by decide
  have hdescent : baseEnd_1037487 < baseStart_1037487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037566 : List Nat := [4, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_1037566 : Nat := 118140960795 + 1037566 * 2 ^ 59
def prefixEnd_1037566 : Nat := 4983230072969 + 3 ^ 40 * 1037566 * 2
def baseEnd_1037566 : Nat := 236786697227996778645923

theorem tailTrace_1037566 : CollatzResearch.WordTrace tailWord_1037566 prefixEnd_1037566 236786697227996778645923 := by
  unfold tailWord_1037566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4730392619885382376265569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25228760639388706006749701 4730392619885382376265569)
  ·
    refine ⟨3547794464914036782199177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4730392619885382376265569 3547794464914036782199177)
    ·
      refine ⟨2660845848685527586649383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3547794464914036782199177 2660845848685527586649383)
      ·
        refine ⟨3991268773028291379974075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2660845848685527586649383 3991268773028291379974075)
        ·
          refine ⟨5986903159542437069961113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3991268773028291379974075 5986903159542437069961113)
          ·
            refine ⟨4490177369656827802470835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5986903159542437069961113 4490177369656827802470835)
            ·
              refine ⟨6735266054485241703706253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4490177369656827802470835 6735266054485241703706253)
              ·
                refine ⟨2525724770431965638889845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6735266054485241703706253 2525724770431965638889845)
                ·
                  refine ⟨236786697227996778645923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2525724770431965638889845 236786697227996778645923)
                  ·
                    rfl

theorem cell21_1037566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_1037566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1037566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1037566 prefixEnd_1037566 := by exact prefixLift 1037566
  have htrace : WordTrace (prefixWord ++ tailWord_1037566) baseStart_1037566 baseEnd_1037566 := by
    simpa [prefixWord, tailWord_1037566, baseEnd_1037566] using wordTrace_append hprefix tailTrace_1037566
  have hstable : (prefixWord ++ tailWord_1037566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037566).length < 2 ^ (prefixWord ++ tailWord_1037566).sum := by decide
  have hdescent : baseEnd_1037566 < baseStart_1037566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037586 : List Nat := [3, 2, 4, 2, 1, 2, 2, 5]
def baseStart_1037586 : Nat := 118140960795 + 1037586 * 2 ^ 59
def prefixEnd_1037586 : Nat := 4983230072969 + 3 ^ 40 * 1037586 * 2
def baseEnd_1037586 : Nat := 78930420500160396104183

theorem tailTrace_1037586 : CollatzResearch.WordTrace tailWord_1037586 prefixEnd_1037586 78930420500160396104183 := by
  unfold tailWord_1037586
  simp only [CollatzResearch.WordTrace]
  refine ⟨9460967604752650606463153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25229246946007068283901741 9460967604752650606463153)
  ·
    refine ⟨7095725703564487954847365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9460967604752650606463153 7095725703564487954847365)
    ·
      refine ⟨1330448569418341491533881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7095725703564487954847365 1330448569418341491533881)
      ·
        refine ⟨997836427063756118650411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1330448569418341491533881 997836427063756118650411)
        ·
          refine ⟨1496754640595634177975617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997836427063756118650411 1496754640595634177975617)
          ·
            refine ⟨1122565980446725633481713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1496754640595634177975617 1122565980446725633481713)
            ·
              refine ⟨841924485335044225111285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1122565980446725633481713 841924485335044225111285)
              ·
                refine ⟨78930420500160396104183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 841924485335044225111285 78930420500160396104183)
                ·
                  rfl

theorem cell21_1037586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_1037586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1037586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1037586 prefixEnd_1037586 := by exact prefixLift 1037586
  have htrace : WordTrace (prefixWord ++ tailWord_1037586) baseStart_1037586 baseEnd_1037586 := by
    simpa [prefixWord, tailWord_1037586, baseEnd_1037586] using wordTrace_append hprefix tailTrace_1037586
  have hstable : (prefixWord ++ tailWord_1037586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037586).length < 2 ^ (prefixWord ++ tailWord_1037586).sum := by decide
  have hdescent : baseEnd_1037586 < baseStart_1037586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037600 : List Nat := [2, 1, 1, 5, 3, 2, 1, 3, 3]
def baseStart_1037600 : Nat := 118140960795 + 1037600 * 2 ^ 59
def prefixEnd_1037600 : Nat := 4983230072969 + 3 ^ 40 * 1037600 * 2
def baseEnd_1037600 : Nat := 236794456491220275079187

theorem tailTrace_1037600 : CollatzResearch.WordTrace tailWord_1037600 prefixEnd_1037600 236794456491220275079187 := by
  unfold tailWord_1037600
  simp only [CollatzResearch.WordTrace]
  refine ⟨18922190520479941408431127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25229587360639921877908169 18922190520479941408431127)
  ·
    refine ⟨28383285780719912112646691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18922190520479941408431127 28383285780719912112646691)
    ·
      refine ⟨42574928671079868168970037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28383285780719912112646691 42574928671079868168970037)
      ·
        refine ⟨3991399562913737640840941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42574928671079868168970037 3991399562913737640840941)
        ·
          refine ⟨1496774836092651615315353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3991399562913737640840941 1496774836092651615315353)
          ·
            refine ⟨1122581127069488711486515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1496774836092651615315353 1122581127069488711486515)
            ·
              refine ⟨1683871690604233067229773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122581127069488711486515 1683871690604233067229773)
              ·
                refine ⟨631451883976587400211165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1683871690604233067229773 631451883976587400211165)
                ·
                  refine ⟨236794456491220275079187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 631451883976587400211165 236794456491220275079187)
                  ·
                    rfl

theorem cell21_1037600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 3].length) (baseStart_1037600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1037600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1037600 prefixEnd_1037600 := by exact prefixLift 1037600
  have htrace : WordTrace (prefixWord ++ tailWord_1037600) baseStart_1037600 baseEnd_1037600 := by
    simpa [prefixWord, tailWord_1037600, baseEnd_1037600] using wordTrace_append hprefix tailTrace_1037600
  have hstable : (prefixWord ++ tailWord_1037600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037600).length < 2 ^ (prefixWord ++ tailWord_1037600).sum := by decide
  have hdescent : baseEnd_1037600 < baseStart_1037600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037676 : List Nat := [2, 2, 1, 1, 5, 3, 2, 2, 3]
def baseStart_1037676 : Nat := 118140960795 + 1037676 * 2 ^ 59
def prefixEnd_1037676 : Nat := 4983230072969 + 3 ^ 40 * 1037676 * 2
def baseEnd_1037676 : Nat := 236811800726661031812365

theorem tailTrace_1037676 : CollatzResearch.WordTrace tailWord_1037676 prefixEnd_1037676 236811800726661031812365 := by
  unfold tailWord_1037676
  simp only [CollatzResearch.WordTrace]
  refine ⟨18923576494342273898314441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25231435325789698531085921 18923576494342273898314441)
  ·
    refine ⟨14192682370756705423735831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18923576494342273898314441 14192682370756705423735831)
    ·
      refine ⟨21289023556135058135603747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14192682370756705423735831 21289023556135058135603747)
      ·
        refine ⟨31933535334202587203405621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21289023556135058135603747 31933535334202587203405621)
        ·
          refine ⟨2993768937581492550319277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31933535334202587203405621 2993768937581492550319277)
          ·
            refine ⟨1122663351593059706369729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2993768937581492550319277 1122663351593059706369729)
            ·
              refine ⟨841997513694794779777297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1122663351593059706369729 841997513694794779777297)
              ·
                refine ⟨631498135271096084832973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 841997513694794779777297 631498135271096084832973)
                ·
                  refine ⟨236811800726661031812365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 631498135271096084832973 236811800726661031812365)
                  ·
                    rfl

theorem cell21_1037676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_1037676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1037676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1037676 prefixEnd_1037676 := by exact prefixLift 1037676
  have htrace : WordTrace (prefixWord ++ tailWord_1037676) baseStart_1037676 baseEnd_1037676 := by
    simpa [prefixWord, tailWord_1037676, baseEnd_1037676] using wordTrace_append hprefix tailTrace_1037676
  have hstable : (prefixWord ++ tailWord_1037676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037676).length < 2 ^ (prefixWord ++ tailWord_1037676).sum := by decide
  have hdescent : baseEnd_1037676 < baseStart_1037676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037780 : List Nat := [2, 4, 1, 2, 4, 1, 7]
def baseStart_1037780 : Nat := 118140960795 + 1037780 * 2 ^ 59
def prefixEnd_1037780 : Nat := 4983230072969 + 3 ^ 40 * 1037780 * 2
def baseEnd_1037780 : Nat := 26315059438175551342091

theorem tailTrace_1037780 : CollatzResearch.WordTrace tailWord_1037780 prefixEnd_1037780 26315059438175551342091 := by
  unfold tailWord_1037780
  simp only [CollatzResearch.WordTrace]
  refine ⟨18925473090153886779207397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25233964120205182372276529 18925473090153886779207397)
  ·
    refine ⟨3548526204403853771101387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18925473090153886779207397 3548526204403853771101387)
    ·
      refine ⟨5322789306605780656652081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3548526204403853771101387 5322789306605780656652081)
      ·
        refine ⟨3992091979954335492489061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5322789306605780656652081 3992091979954335492489061)
        ·
          refine ⟨748517246241437904841699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3992091979954335492489061 748517246241437904841699)
          ·
            refine ⟨1122775869362156857262549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748517246241437904841699 1122775869362156857262549)
            ·
              refine ⟨26315059438175551342091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1122775869362156857262549 26315059438175551342091)
              ·
                rfl

theorem cell21_1037780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 7].length) (baseStart_1037780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1037780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1037780 prefixEnd_1037780 := by exact prefixLift 1037780
  have htrace : WordTrace (prefixWord ++ tailWord_1037780) baseStart_1037780 baseEnd_1037780 := by
    simpa [prefixWord, tailWord_1037780, baseEnd_1037780] using wordTrace_append hprefix tailTrace_1037780
  have hstable : (prefixWord ++ tailWord_1037780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037780).length < 2 ^ (prefixWord ++ tailWord_1037780).sum := by decide
  have hdescent : baseEnd_1037780 < baseStart_1037780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037791 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 6]
def baseStart_1037791 : Nat := 118140960795 + 1037791 * 2 ^ 59
def prefixEnd_1037791 : Nat := 4983230072969 + 3 ^ 40 * 1037791 * 2
def baseEnd_1037791 : Nat := 236838045293446387395463

theorem tailTrace_1037791 : CollatzResearch.WordTrace tailWord_1037791 prefixEnd_1037791 236838045293446387395463 := by
  unfold tailWord_1037791
  simp only [CollatzResearch.WordTrace]
  refine ⟨37851347383267922437065227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25234231588845281624710151 37851347383267922437065227)
  ·
    refine ⟨56777021074901883655597841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37851347383267922437065227 56777021074901883655597841)
    ·
      refine ⟨42582765806176412741698381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56777021074901883655597841 42582765806176412741698381)
      ·
        refine ⟨15968537177316154778136893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42582765806176412741698381 15968537177316154778136893)
        ·
          refine ⟨5988201441493558041801335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15968537177316154778136893 5988201441493558041801335)
          ·
            refine ⟨8982302162240337062702003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5988201441493558041801335 8982302162240337062702003)
            ·
              refine ⟨13473453243360505594053005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8982302162240337062702003 13473453243360505594053005)
              ·
                refine ⟨5052544966260189597769877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13473453243360505594053005 5052544966260189597769877)
                ·
                  refine ⟨236838045293446387395463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5052544966260189597769877 236838045293446387395463)
                  ·
                    rfl

theorem cell21_1037791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 6].length) (baseStart_1037791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1037791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1037791 prefixEnd_1037791 := by exact prefixLift 1037791
  have htrace : WordTrace (prefixWord ++ tailWord_1037791) baseStart_1037791 baseEnd_1037791 := by
    simpa [prefixWord, tailWord_1037791, baseEnd_1037791] using wordTrace_append hprefix tailTrace_1037791
  have hstable : (prefixWord ++ tailWord_1037791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037791).length < 2 ^ (prefixWord ++ tailWord_1037791).sum := by decide
  have hdescent : baseEnd_1037791 < baseStart_1037791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037808 : List Nat := [2, 1, 1, 1, 3, 5, 1, 3, 4]
def baseStart_1037808 : Nat := 118140960795 + 1037808 * 2 ^ 59
def prefixEnd_1037808 : Nat := 4983230072969 + 3 ^ 40 * 1037808 * 2
def baseEnd_1037808 : Nat := 236841924925058135612095

theorem tailTrace_1037808 : CollatzResearch.WordTrace tailWord_1037808 prefixEnd_1037808 236841924925058135612095 := by
  unfold tailWord_1037808
  simp only [CollatzResearch.WordTrace]
  refine ⟨18925983712103167170217039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25234644949470889560289385 18925983712103167170217039)
  ·
    refine ⟨28388975568154750755325559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18925983712103167170217039 28388975568154750755325559)
    ·
      refine ⟨42583463352232126132988339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28388975568154750755325559 42583463352232126132988339)
      ·
        refine ⟨63875195028348189199482509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42583463352232126132988339 63875195028348189199482509)
        ·
          refine ⟨23953198135630570949805941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63875195028348189199482509 23953198135630570949805941)
          ·
            refine ⟨2245612325215366026544307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23953198135630570949805941 2245612325215366026544307)
            ·
              refine ⟨3368418487823049039816461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2245612325215366026544307 3368418487823049039816461)
              ·
                refine ⟨1263156932933643389931173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3368418487823049039816461 1263156932933643389931173)
                ·
                  refine ⟨236841924925058135612095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1263156932933643389931173 236841924925058135612095)
                  ·
                    rfl

theorem cell21_1037808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 4].length) (baseStart_1037808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1037808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1037808 prefixEnd_1037808 := by exact prefixLift 1037808
  have htrace : WordTrace (prefixWord ++ tailWord_1037808) baseStart_1037808 baseEnd_1037808 := by
    simpa [prefixWord, tailWord_1037808, baseEnd_1037808] using wordTrace_append hprefix tailTrace_1037808
  have hstable : (prefixWord ++ tailWord_1037808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037808).length < 2 ^ (prefixWord ++ tailWord_1037808).sum := by decide
  have hdescent : baseEnd_1037808 < baseStart_1037808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037853 : List Nat := [1, 4, 2, 2, 1, 1, 2, 3, 5]
def baseStart_1037853 : Nat := 118140960795 + 1037853 * 2 ^ 59
def prefixEnd_1037853 : Nat := 4983230072969 + 3 ^ 40 * 1037853 * 2
def baseEnd_1037853 : Nat := 236852194538148057362003

theorem tailTrace_1037853 : CollatzResearch.WordTrace tailWord_1037853 prefixEnd_1037853 236852194538148057362003 := by
  unfold tailWord_1037853
  simp only [CollatzResearch.WordTrace]
  refine ⟨37853608709043307025822213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25235739139362204683881475 37853608709043307025822213)
  ·
    refine ⟨7097551632945620067341665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37853608709043307025822213 7097551632945620067341665)
    ·
      refine ⟨5323163724709215050506249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7097551632945620067341665 5323163724709215050506249)
      ·
        refine ⟨3992372793531911287879687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5323163724709215050506249 3992372793531911287879687)
        ·
          refine ⟨5988559190297866931819531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3992372793531911287879687 5988559190297866931819531)
          ·
            refine ⟨8982838785446800397729297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5988559190297866931819531 8982838785446800397729297)
            ·
              refine ⟨6737129089085100298296973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8982838785446800397729297 6737129089085100298296973)
              ·
                refine ⟨2526423408406912611861365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6737129089085100298296973 2526423408406912611861365)
                ·
                  refine ⟨236852194538148057362003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2526423408406912611861365 236852194538148057362003)
                  ·
                    rfl

theorem cell21_1037853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_1037853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1037853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1037853 prefixEnd_1037853 := by exact prefixLift 1037853
  have htrace : WordTrace (prefixWord ++ tailWord_1037853) baseStart_1037853 baseEnd_1037853 := by
    simpa [prefixWord, tailWord_1037853, baseEnd_1037853] using wordTrace_append hprefix tailTrace_1037853
  have hstable : (prefixWord ++ tailWord_1037853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037853).length < 2 ^ (prefixWord ++ tailWord_1037853).sum := by decide
  have hdescent : baseEnd_1037853 < baseStart_1037853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037870 : List Nat := [4, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_1037870 : Nat := 118140960795 + 1037870 * 2 ^ 59
def prefixEnd_1037870 : Nat := 4983230072969 + 3 ^ 40 * 1037870 * 2
def baseEnd_1037870 : Nat := 236856074169759805578635

theorem tailTrace_1037870 : CollatzResearch.WordTrace tailWord_1037870 prefixEnd_1037870 236856074169759805578635 := by
  unfold tailWord_1037870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4731778593747714866148883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25236152499987812619460709 4731778593747714866148883)
  ·
    refine ⟨7097667890621572299223325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4731778593747714866148883 7097667890621572299223325)
    ·
      refine ⟨2661625458983089612208747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7097667890621572299223325 2661625458983089612208747)
      ·
        refine ⟨3992438188474634418313121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2661625458983089612208747 3992438188474634418313121)
        ·
          refine ⟨2994328641355975813734841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3992438188474634418313121 2994328641355975813734841)
          ·
            refine ⟨2245746481016981860301131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2994328641355975813734841 2245746481016981860301131)
            ·
              refine ⟨3368619721525472790451697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2245746481016981860301131 3368619721525472790451697)
              ·
                refine ⟨2526464791144104592838773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3368619721525472790451697 2526464791144104592838773)
                ·
                  refine ⟨236856074169759805578635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2526464791144104592838773 236856074169759805578635)
                  ·
                    rfl

theorem cell21_1037870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_1037870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1037870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1037870 prefixEnd_1037870 := by exact prefixLift 1037870
  have htrace : WordTrace (prefixWord ++ tailWord_1037870) baseStart_1037870 baseEnd_1037870 := by
    simpa [prefixWord, tailWord_1037870, baseEnd_1037870] using wordTrace_append hprefix tailTrace_1037870
  have hstable : (prefixWord ++ tailWord_1037870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037870).length < 2 ^ (prefixWord ++ tailWord_1037870).sum := by decide
  have hdescent : baseEnd_1037870 < baseStart_1037870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037901 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1037901 : Nat := 118140960795 + 1037901 * 2 ^ 59
def prefixEnd_1037901 : Nat := 4983230072969 + 3 ^ 40 * 1037901 * 2
def baseEnd_1037901 : Nat := 236863148792110640561905

theorem tailTrace_1037901 : CollatzResearch.WordTrace tailWord_1037901 prefixEnd_1037901 236863148792110640561905 := by
  unfold tailWord_1037901
  simp only [CollatzResearch.WordTrace]
  refine ⟨37855359412869411223569557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25236906275246274149046371 37855359412869411223569557)
  ·
    refine ⟨1774469972478253651104823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37855359412869411223569557 1774469972478253651104823)
    ·
      refine ⟨2661704958717380476657235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1774469972478253651104823 2661704958717380476657235)
      ·
        refine ⟨3992557438076070714985853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2661704958717380476657235 3992557438076070714985853)
        ·
          refine ⟨1497209039278526518119695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3992557438076070714985853 1497209039278526518119695)
          ·
            refine ⟨2245813558917789777179543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497209039278526518119695 2245813558917789777179543)
            ·
              refine ⟨3368720338376684665769315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2245813558917789777179543 3368720338376684665769315)
              ·
                refine ⟨5053080507565026998653973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3368720338376684665769315 5053080507565026998653973)
                ·
                  refine ⟨236863148792110640561905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5053080507565026998653973 236863148792110640561905)
                  ·
                    rfl

theorem cell21_1037901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1037901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1037901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1037901 prefixEnd_1037901 := by exact prefixLift 1037901
  have htrace : WordTrace (prefixWord ++ tailWord_1037901) baseStart_1037901 baseEnd_1037901 := by
    simpa [prefixWord, tailWord_1037901, baseEnd_1037901] using wordTrace_append hprefix tailTrace_1037901
  have hstable : (prefixWord ++ tailWord_1037901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037901).length < 2 ^ (prefixWord ++ tailWord_1037901).sum := by decide
  have hdescent : baseEnd_1037901 < baseStart_1037901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038098 : List Nat := [3, 2, 4, 1, 1, 1, 2, 2, 5]
def baseStart_1038098 : Nat := 118140960795 + 1038098 * 2 ^ 59
def prefixEnd_1038098 : Nat := 4983230072969 + 3 ^ 40 * 1038098 * 2
def baseEnd_1038098 : Nat := 236908106876082075778169

theorem tailTrace_1038098 : CollatzResearch.WordTrace tailWord_1038098 prefixEnd_1038098 236908106876082075778169 := by
  unfold tailWord_1038098
  simp only [CollatzResearch.WordTrace]
  refine ⟨9465636148288928467122737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25241696395437142578993965 9465636148288928467122737)
  ·
    refine ⟨7099227111216696350342053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9465636148288928467122737 7099227111216696350342053)
    ·
      refine ⟨1331105083353130565689135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7099227111216696350342053 1331105083353130565689135)
      ·
        refine ⟨1996657625029695848533703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1331105083353130565689135 1996657625029695848533703)
        ·
          refine ⟨2994986437544543772800555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1996657625029695848533703 2994986437544543772800555)
          ·
            refine ⟨4492479656316815659200833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994986437544543772800555 4492479656316815659200833)
            ·
              refine ⟨3369359742237611744400625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4492479656316815659200833 3369359742237611744400625)
              ·
                refine ⟨2527019806678208808300469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3369359742237611744400625 2527019806678208808300469)
                ·
                  refine ⟨236908106876082075778169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2527019806678208808300469 236908106876082075778169)
                  ·
                    rfl

theorem cell21_1038098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_1038098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038098 prefixEnd_1038098 := by exact prefixLift 1038098
  have htrace : WordTrace (prefixWord ++ tailWord_1038098) baseStart_1038098 baseEnd_1038098 := by
    simpa [prefixWord, tailWord_1038098, baseEnd_1038098] using wordTrace_append hprefix tailTrace_1038098
  have hstable : (prefixWord ++ tailWord_1038098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038098).length < 2 ^ (prefixWord ++ tailWord_1038098).sum := by decide
  have hdescent : baseEnd_1038098 < baseStart_1038098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038132 : List Nat := [2, 5, 1, 1, 2, 2, 3, 2, 3]
def baseStart_1038132 : Nat := 118140960795 + 1038132 * 2 ^ 59
def prefixEnd_1038132 : Nat := 4983230072969 + 3 ^ 40 * 1038132 * 2
def baseEnd_1038132 : Nat := 236915866139305572211433

theorem tailTrace_1038132 : CollatzResearch.WordTrace tailWord_1038132 prefixEnd_1038132 236915866139305572211433 := by
  unfold tailWord_1038132
  simp only [CollatzResearch.WordTrace]
  refine ⟨18931892337516268837614325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25242523116688358450152433 18931892337516268837614325)
  ·
    refine ⟨1774864906642150203526343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18931892337516268837614325 1774864906642150203526343)
    ·
      refine ⟨2662297359963225305289515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1774864906642150203526343 2662297359963225305289515)
      ·
        refine ⟨3993446039944837957934273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662297359963225305289515 3993446039944837957934273)
        ·
          refine ⟨2995084529958628468450705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3993446039944837957934273 2995084529958628468450705)
          ·
            refine ⟨2246313397468971351338029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2995084529958628468450705 2246313397468971351338029)
            ·
              refine ⟨842367524050864256751761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2246313397468971351338029 842367524050864256751761)
              ·
                refine ⟨631775643038148192563821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842367524050864256751761 631775643038148192563821)
                ·
                  refine ⟨236915866139305572211433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 631775643038148192563821 236915866139305572211433)
                  ·
                    rfl

theorem cell21_1038132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_1038132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038132 prefixEnd_1038132 := by exact prefixLift 1038132
  have htrace : WordTrace (prefixWord ++ tailWord_1038132) baseStart_1038132 baseEnd_1038132 := by
    simpa [prefixWord, tailWord_1038132, baseEnd_1038132] using wordTrace_append hprefix tailTrace_1038132
  have hstable : (prefixWord ++ tailWord_1038132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038132).length < 2 ^ (prefixWord ++ tailWord_1038132).sum := by decide
  have hdescent : baseEnd_1038132 < baseStart_1038132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038188 : List Nat := [2, 2, 1, 1, 4, 3, 2, 2, 4]
def baseStart_1038188 : Nat := 118140960795 + 1038188 * 2 ^ 59
def prefixEnd_1038188 : Nat := 4983230072969 + 3 ^ 40 * 1038188 * 2
def baseEnd_1038188 : Nat := 236928646102261919277985

theorem tailTrace_1038188 : CollatzResearch.WordTrace tailWord_1038188 prefixEnd_1038188 236928646102261919277985 := by
  unfold tailWord_1038188
  simp only [CollatzResearch.WordTrace]
  refine ⟨18932913581414829619633609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25243884775219772826178145 18932913581414829619633609)
  ·
    refine ⟨14199685186061122214725207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18932913581414829619633609 14199685186061122214725207)
    ·
      refine ⟨21299527779091683322087811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14199685186061122214725207 21299527779091683322087811)
      ·
        refine ⟨31949291668637524983131717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21299527779091683322087811 31949291668637524983131717)
        ·
          refine ⟨5990492187869535934337197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31949291668637524983131717 5990492187869535934337197)
          ·
            refine ⟨2246434570451075975376449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5990492187869535934337197 2246434570451075975376449)
            ·
              refine ⟨1684825927838306981532337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2246434570451075975376449 1684825927838306981532337)
              ·
                refine ⟨1263619445878730236149253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1684825927838306981532337 1263619445878730236149253)
                ·
                  refine ⟨236928646102261919277985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1263619445878730236149253 236928646102261919277985)
                  ·
                    rfl

theorem cell21_1038188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_1038188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038188 prefixEnd_1038188 := by exact prefixLift 1038188
  have htrace : WordTrace (prefixWord ++ tailWord_1038188) baseStart_1038188 baseEnd_1038188 := by
    simpa [prefixWord, tailWord_1038188, baseEnd_1038188] using wordTrace_append hprefix tailTrace_1038188
  have hstable : (prefixWord ++ tailWord_1038188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038188).length < 2 ^ (prefixWord ++ tailWord_1038188).sum := by decide
  have hdescent : baseEnd_1038188 < baseStart_1038188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038233 : List Nat := [1, 2, 1, 2, 1, 3, 3, 5, 3]
def baseStart_1038233 : Nat := 118140960795 + 1038233 * 2 ^ 59
def prefixEnd_1038233 : Nat := 4983230072969 + 3 ^ 40 * 1038233 * 2
def baseEnd_1038233 : Nat := 236938915715351841027893

theorem tailTrace_1038233 : CollatzResearch.WordTrace tailWord_1038233 prefixEnd_1038233 236938915715351841027893 := by
  unfold tailWord_1038233
  simp only [CollatzResearch.WordTrace]
  refine ⟨37867468447666631924655353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25244978965111087949770235 37867468447666631924655353)
  ·
    refine ⟨28400601335749973943491515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37867468447666631924655353 28400601335749973943491515)
    ·
      refine ⟨42600902003624960915237273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28400601335749973943491515 42600902003624960915237273)
      ·
        refine ⟨31950676502718720686427955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42600902003624960915237273 31950676502718720686427955)
        ·
          refine ⟨47926014754078081029641933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31950676502718720686427955 47926014754078081029641933)
          ·
            refine ⟨17972255532779280386115725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47926014754078081029641933 17972255532779280386115725)
            ·
              refine ⟨6739595824792230144793397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17972255532779280386115725 6739595824792230144793397)
              ·
                refine ⟨631837108574271576074381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6739595824792230144793397 631837108574271576074381)
                ·
                  refine ⟨236938915715351841027893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 631837108574271576074381 236938915715351841027893)
                  ·
                    rfl

theorem cell21_1038233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 3].length) (baseStart_1038233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038233 prefixEnd_1038233 := by exact prefixLift 1038233
  have htrace : WordTrace (prefixWord ++ tailWord_1038233) baseStart_1038233 baseEnd_1038233 := by
    simpa [prefixWord, tailWord_1038233, baseEnd_1038233] using wordTrace_append hprefix tailTrace_1038233
  have hstable : (prefixWord ++ tailWord_1038233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038233).length < 2 ^ (prefixWord ++ tailWord_1038233).sum := by decide
  have hdescent : baseEnd_1038233 < baseStart_1038233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038264 : List Nat := [2, 1, 2, 1, 2, 3, 5, 1, 4]
def baseStart_1038264 : Nat := 118140960795 + 1038264 * 2 ^ 59
def prefixEnd_1038264 : Nat := 4983230072969 + 3 ^ 40 * 1038264 * 2
def baseEnd_1038264 : Nat := 236945990337702676011163

theorem tailTrace_1038264 : CollatzResearch.WordTrace tailWord_1038264 prefixEnd_1038264 236945990337702676011163 := by
  unfold tailWord_1038264
  simp only [CollatzResearch.WordTrace]
  refine ⟨18934299555277162109516923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25245732740369549479355897 18934299555277162109516923)
  ·
    refine ⟨28401449332915743164275385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18934299555277162109516923 28401449332915743164275385)
    ·
      refine ⟨21301086999686807373206539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28401449332915743164275385 21301086999686807373206539)
      ·
        refine ⟨31951630499530211059809809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21301086999686807373206539 31951630499530211059809809)
        ·
          refine ⟨23963722874647658294857357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31951630499530211059809809 23963722874647658294857357)
          ·
            refine ⟨8986396077992871860571509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23963722874647658294857357 8986396077992871860571509)
            ·
              refine ⟨842474632311831736928579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8986396077992871860571509 842474632311831736928579)
              ·
                refine ⟨1263711948467747605392869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842474632311831736928579 1263711948467747605392869)
                ·
                  refine ⟨236945990337702676011163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1263711948467747605392869 236945990337702676011163)
                  ·
                    rfl

theorem cell21_1038264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 4].length) (baseStart_1038264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038264 prefixEnd_1038264 := by exact prefixLift 1038264
  have htrace : WordTrace (prefixWord ++ tailWord_1038264) baseStart_1038264 baseEnd_1038264 := by
    simpa [prefixWord, tailWord_1038264, baseEnd_1038264] using wordTrace_append hprefix tailTrace_1038264
  have hstable : (prefixWord ++ tailWord_1038264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038264).length < 2 ^ (prefixWord ++ tailWord_1038264).sum := by decide
  have hdescent : baseEnd_1038264 < baseStart_1038264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038337 : List Nat := [1, 2, 4, 1, 2, 1, 1, 9]
def baseStart_1038337 : Nat := 118140960795 + 1038337 * 2 ^ 59
def prefixEnd_1038337 : Nat := 4983230072969 + 3 ^ 40 * 1038337 * 2
def baseEnd_1038337 : Nat := 78987549977423590431449

theorem tailTrace_1038337 : CollatzResearch.WordTrace tailWord_1038337 prefixEnd_1038337 78987549977423590431449 := by
  unfold tailWord_1038337
  simp only [CollatzResearch.WordTrace]
  refine ⟨37871261639289857686441265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25247507759526571790960843 37871261639289857686441265)
  ·
    refine ⟨28403446229467393264830949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37871261639289857686441265 28403446229467393264830949)
    ·
      refine ⟨5325646168025136237155803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28403446229467393264830949 5325646168025136237155803)
      ·
        refine ⟨7988469252037704355733705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5325646168025136237155803 7988469252037704355733705)
        ·
          refine ⟨5991351939028278266800279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7988469252037704355733705 5991351939028278266800279)
          ·
            refine ⟨8987027908542417400200419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5991351939028278266800279 8987027908542417400200419)
            ·
              refine ⟨13480541862813626100300629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8987027908542417400200419 13480541862813626100300629)
              ·
                refine ⟨78987549977423590431449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13480541862813626100300629 78987549977423590431449)
                ·
                  rfl

theorem cell21_1038337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 9].length) (baseStart_1038337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038337 prefixEnd_1038337 := by exact prefixLift 1038337
  have htrace : WordTrace (prefixWord ++ tailWord_1038337) baseStart_1038337 baseEnd_1038337 := by
    simpa [prefixWord, tailWord_1038337, baseEnd_1038337] using wordTrace_append hprefix tailTrace_1038337
  have hstable : (prefixWord ++ tailWord_1038337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038337).length < 2 ^ (prefixWord ++ tailWord_1038337).sum := by decide
  have hdescent : baseEnd_1038337 < baseStart_1038337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038354 : List Nat := [3, 2, 5, 11]
def baseStart_1038354 : Nat := 118140960795 + 1038354 * 2 ^ 59
def prefixEnd_1038354 : Nat := 4983230072969 + 3 ^ 40 * 1038354 * 2
def baseEnd_1038354 : Nat := 975170903555072096753

theorem tailTrace_1038354 : CollatzResearch.WordTrace tailWord_1038354 prefixEnd_1038354 975170903555072096753 := by
  unfold tailWord_1038354
  simp only [CollatzResearch.WordTrace]
  refine ⟨9467970420057067397452529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25247921120152179726540077 9467970420057067397452529)
  ·
    refine ⟨7100977815042800548089397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9467970420057067397452529 7100977815042800548089397)
    ·
      refine ⟨665716670160262551383381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7100977815042800548089397 665716670160262551383381)
      ·
        refine ⟨975170903555072096753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 665716670160262551383381 975170903555072096753)
        ·
          rfl

theorem cell21_1038354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 11].length) (baseStart_1038354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038354 prefixEnd_1038354 := by exact prefixLift 1038354
  have htrace : WordTrace (prefixWord ++ tailWord_1038354) baseStart_1038354 baseEnd_1038354 := by
    simpa [prefixWord, tailWord_1038354, baseEnd_1038354] using wordTrace_append hprefix tailTrace_1038354
  have hstable : (prefixWord ++ tailWord_1038354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038354).length < 2 ^ (prefixWord ++ tailWord_1038354).sum := by decide
  have hdescent : baseEnd_1038354 < baseStart_1038354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038388 : List Nat := [2, 5, 1, 2, 2, 1, 3, 5]
def baseStart_1038388 : Nat := 118140960795 + 1038388 * 2 ^ 59
def prefixEnd_1038388 : Nat := 4983230072969 + 3 ^ 40 * 1038388 * 2
def baseEnd_1038388 : Nat := 78991429609035338648081

theorem tailTrace_1038388 : CollatzResearch.WordTrace tailWord_1038388 prefixEnd_1038388 78991429609035338648081 := by
  unfold tailWord_1038388
  simp only [CollatzResearch.WordTrace]
  refine ⟨18936560881052546698273909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25248747841403395597698545 18936560881052546698273909)
  ·
    refine ⟨1775302582598676252963179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18936560881052546698273909 1775302582598676252963179)
    ·
      refine ⟨2662953873898014379444769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1775302582598676252963179 2662953873898014379444769)
      ·
        refine ⟨1997215405423510784583577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2662953873898014379444769 1997215405423510784583577)
        ·
          refine ⟨1497911554067633088437683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1997215405423510784583577 1497911554067633088437683)
          ·
            refine ⟨2246867331101449632656525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497911554067633088437683 2246867331101449632656525)
            ·
              refine ⟨842575249163043612246197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2246867331101449632656525 842575249163043612246197)
              ·
                refine ⟨78991429609035338648081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 842575249163043612246197 78991429609035338648081)
                ·
                  rfl

theorem cell21_1038388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 5].length) (baseStart_1038388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038388 prefixEnd_1038388 := by exact prefixLift 1038388
  have htrace : WordTrace (prefixWord ++ tailWord_1038388) baseStart_1038388 baseEnd_1038388 := by
    simpa [prefixWord, tailWord_1038388, baseEnd_1038388] using wordTrace_append hprefix tailTrace_1038388
  have hstable : (prefixWord ++ tailWord_1038388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038388).length < 2 ^ (prefixWord ++ tailWord_1038388).sum := by decide
  have hdescent : baseEnd_1038388 < baseStart_1038388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038444 : List Nat := [2, 2, 1, 1, 3, 3, 2, 2, 5]
def baseStart_1038444 : Nat := 118140960795 + 1038444 * 2 ^ 59
def prefixEnd_1038444 : Nat := 4983230072969 + 3 ^ 40 * 1038444 * 2
def baseEnd_1038444 : Nat := 236987068790062363010795

theorem tailTrace_1038444 : CollatzResearch.WordTrace tailWord_1038444 prefixEnd_1038444 236987068790062363010795 := by
  unfold tailWord_1038444
  simp only [CollatzResearch.WordTrace]
  refine ⟨18937582124951107480293193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25250109499934809973724257 18937582124951107480293193)
  ·
    refine ⟨14203186593713330610219895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18937582124951107480293193 14203186593713330610219895)
    ·
      refine ⟨21304779890569995915329843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14203186593713330610219895 21304779890569995915329843)
      ·
        refine ⟨31957169835854993872994765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21304779890569995915329843 31957169835854993872994765)
        ·
          refine ⟨11983938688445622702373037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31957169835854993872994765 11983938688445622702373037)
          ·
            refine ⟨4493977008167108513389889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11983938688445622702373037 4493977008167108513389889)
            ·
              refine ⟨3370482756125331385042417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4493977008167108513389889 3370482756125331385042417)
              ·
                refine ⟨2527862067093998538781813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3370482756125331385042417 2527862067093998538781813)
                ·
                  refine ⟨236987068790062363010795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2527862067093998538781813 236987068790062363010795)
                  ·
                    rfl

theorem cell21_1038444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_1038444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038444 prefixEnd_1038444 := by exact prefixLift 1038444
  have htrace : WordTrace (prefixWord ++ tailWord_1038444) baseStart_1038444 baseEnd_1038444 := by
    simpa [prefixWord, tailWord_1038444, baseEnd_1038444] using wordTrace_append hprefix tailTrace_1038444
  have hstable : (prefixWord ++ tailWord_1038444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038444).length < 2 ^ (prefixWord ++ tailWord_1038444).sum := by decide
  have hdescent : baseEnd_1038444 < baseStart_1038444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038478 : List Nat := [4, 1, 1, 3, 3, 2, 1, 1, 5]
def baseStart_1038478 : Nat := 118140960795 + 1038478 * 2 ^ 59
def prefixEnd_1038478 : Nat := 4983230072969 + 3 ^ 40 * 1038478 * 2
def baseEnd_1038478 : Nat := 236994828053285859444059

theorem tailTrace_1038478 : CollatzResearch.WordTrace tailWord_1038478 prefixEnd_1038478 236994828053285859444059 := by
  unfold tailWord_1038478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4734550541472379845915511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25250936221186025844882725 4734550541472379845915511)
  ·
    refine ⟨7101825812208569768873267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4734550541472379845915511 7101825812208569768873267)
    ·
      refine ⟨10652738718312854653309901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7101825812208569768873267 10652738718312854653309901)
      ·
        refine ⟨3994777019367320494991213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10652738718312854653309901 3994777019367320494991213)
        ·
          refine ⟨1498041382262745185621705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3994777019367320494991213 1498041382262745185621705)
          ·
            refine ⟨1123531036697058889216279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1498041382262745185621705 1123531036697058889216279)
            ·
              refine ⟨1685296555045588333824419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123531036697058889216279 1685296555045588333824419)
              ·
                refine ⟨2527944832568382500736629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1685296555045588333824419 2527944832568382500736629)
                ·
                  refine ⟨236994828053285859444059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2527944832568382500736629 236994828053285859444059)
                  ·
                    rfl

theorem cell21_1038478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_1038478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038478 prefixEnd_1038478 := by exact prefixLift 1038478
  have htrace : WordTrace (prefixWord ++ tailWord_1038478) baseStart_1038478 baseEnd_1038478 := by
    simpa [prefixWord, tailWord_1038478, baseEnd_1038478] using wordTrace_append hprefix tailTrace_1038478
  have hstable : (prefixWord ++ tailWord_1038478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038478).length < 2 ^ (prefixWord ++ tailWord_1038478).sum := by decide
  have hdescent : baseEnd_1038478 < baseStart_1038478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038529 : List Nat := [1, 2, 6, 1, 3, 1, 2, 2, 3]
def baseStart_1038529 : Nat := 118140960795 + 1038529 * 2 ^ 59
def prefixEnd_1038529 : Nat := 4983230072969 + 3 ^ 40 * 1038529 * 2
def baseEnd_1038529 : Nat := 237006466948121104093955

theorem tailTrace_1038529 : CollatzResearch.WordTrace tailWord_1038529 prefixEnd_1038529 237006466948121104093955 := by
  unfold tailWord_1038529
  simp only [CollatzResearch.WordTrace]
  refine ⟨37878264454594274477430641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25252176303062849651620427 37878264454594274477430641)
  ·
    refine ⟨28408698340945705858072981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37878264454594274477430641 28408698340945705858072981)
    ·
      refine ⟨1331657734731829962097171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28408698340945705858072981 1331657734731829962097171)
      ·
        refine ⟨1997486602097744943145757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1331657734731829962097171 1997486602097744943145757)
        ·
          refine ⟨749057475786654353679659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1997486602097744943145757 749057475786654353679659)
          ·
            refine ⟨1123586213679981530519489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749057475786654353679659 1123586213679981530519489)
            ·
              refine ⟨842689660259986147889617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1123586213679981530519489 842689660259986147889617)
              ·
                refine ⟨632017245194989610917213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842689660259986147889617 632017245194989610917213)
                ·
                  refine ⟨237006466948121104093955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632017245194989610917213 237006466948121104093955)
                  ·
                    rfl

theorem cell21_1038529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 3].length) (baseStart_1038529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038529 prefixEnd_1038529 := by exact prefixLift 1038529
  have htrace : WordTrace (prefixWord ++ tailWord_1038529) baseStart_1038529 baseEnd_1038529 := by
    simpa [prefixWord, tailWord_1038529, baseEnd_1038529] using wordTrace_append hprefix tailTrace_1038529
  have hstable : (prefixWord ++ tailWord_1038529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038529).length < 2 ^ (prefixWord ++ tailWord_1038529).sum := by decide
  have hdescent : baseEnd_1038529 < baseStart_1038529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038540 : List Nat := [2, 2, 1, 6, 2, 1, 1, 6]
def baseStart_1038540 : Nat := 118140960795 + 1038540 * 2 ^ 59
def prefixEnd_1038540 : Nat := 4983230072969 + 3 ^ 40 * 1038540 * 2
def baseEnd_1038540 : Nat := 79002992432662509803533

theorem tailTrace_1038540 : CollatzResearch.WordTrace tailWord_1038540 prefixEnd_1038540 79002992432662509803533 := by
  unfold tailWord_1038540
  simp only [CollatzResearch.WordTrace]
  refine ⟨18939332828777211678040537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25252443771702948904054049 18939332828777211678040537)
  ·
    refine ⟨14204499621582908758530403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18939332828777211678040537 14204499621582908758530403)
    ·
      refine ⟨21306749432374363137795605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14204499621582908758530403 21306749432374363137795605)
      ·
        refine ⟨998753879642548272084169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21306749432374363137795605 998753879642548272084169)
        ·
          refine ⟨749065409731911204063127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 998753879642548272084169 749065409731911204063127)
          ·
            refine ⟨1123598114597866806094691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749065409731911204063127 1123598114597866806094691)
            ·
              refine ⟨1685397171896800209142037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123598114597866806094691 1685397171896800209142037)
              ·
                refine ⟨79002992432662509803533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1685397171896800209142037 79002992432662509803533)
                ·
                  rfl

theorem cell21_1038540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 6].length) (baseStart_1038540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038540 prefixEnd_1038540 := by exact prefixLift 1038540
  have htrace : WordTrace (prefixWord ++ tailWord_1038540) baseStart_1038540 baseEnd_1038540 := by
    simpa [prefixWord, tailWord_1038540, baseEnd_1038540] using wordTrace_append hprefix tailTrace_1038540
  have hstable : (prefixWord ++ tailWord_1038540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038540).length < 2 ^ (prefixWord ++ tailWord_1038540).sum := by decide
  have hdescent : baseEnd_1038540 < baseStart_1038540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038579 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 7]
def baseStart_1038579 : Nat := 118140960795 + 1038579 * 2 ^ 59
def prefixEnd_1038579 : Nat := 4983230072969 + 3 ^ 40 * 1038579 * 2
def baseEnd_1038579 : Nat := 237017877629332128260519

theorem tailTrace_1038579 : CollatzResearch.WordTrace tailWord_1038579 prefixEnd_1038579 237017877629332128260519 := by
  unfold tailWord_1038579
  simp only [CollatzResearch.WordTrace]
  refine ⟨37880088104413133016750791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25253392069608755344500527 37880088104413133016750791)
  ·
    refine ⟨56820132156619699525126187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37880088104413133016750791 56820132156619699525126187)
    ·
      refine ⟨85230198234929549287689281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56820132156619699525126187 85230198234929549287689281)
      ·
        refine ⟨63922648676197161965766961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85230198234929549287689281 63922648676197161965766961)
        ·
          refine ⟨47941986507147871474325221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63922648676197161965766961 47941986507147871474325221)
          ·
            refine ⟨8989122470090225901435979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47941986507147871474325221 8989122470090225901435979)
            ·
              refine ⟨13483683705135338852153969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8989122470090225901435979 13483683705135338852153969)
              ·
                refine ⟨10112762778851504139115477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13483683705135338852153969 10112762778851504139115477)
                ·
                  refine ⟨237017877629332128260519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10112762778851504139115477 237017877629332128260519)
                  ·
                    rfl

theorem cell21_1038579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 7].length) (baseStart_1038579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038579 prefixEnd_1038579 := by exact prefixLift 1038579
  have htrace : WordTrace (prefixWord ++ tailWord_1038579) baseStart_1038579 baseEnd_1038579 := by
    simpa [prefixWord, tailWord_1038579, baseEnd_1038579] using wordTrace_append hprefix tailTrace_1038579
  have hstable : (prefixWord ++ tailWord_1038579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038579).length < 2 ^ (prefixWord ++ tailWord_1038579).sum := by decide
  have hdescent : baseEnd_1038579 < baseStart_1038579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038700 : List Nat := [2, 2, 1, 1, 15]
def baseStart_1038700 : Nat := 118140960795 + 1038700 * 2 ^ 59
def prefixEnd_1038700 : Nat := 4983230072969 + 3 ^ 40 * 1038700 * 2
def baseEnd_1038700 : Nat := 2926487549109417367205

theorem tailTrace_1038700 : CollatzResearch.WordTrace tailWord_1038700 prefixEnd_1038700 2926487549109417367205 := by
  unfold tailWord_1038700
  simp only [CollatzResearch.WordTrace]
  refine ⟨18942250668487385340952777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25256334224649847121270369 18942250668487385340952777)
  ·
    refine ⟨14206688001365539005714583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18942250668487385340952777 14206688001365539005714583)
    ·
      refine ⟨21310032002048308508571875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14206688001365539005714583 21310032002048308508571875)
      ·
        refine ⟨31965048003072462762857813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21310032002048308508571875 31965048003072462762857813)
        ·
          refine ⟨2926487549109417367205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 31965048003072462762857813 2926487549109417367205)
          ·
            rfl

theorem cell21_1038700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 15].length) (baseStart_1038700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038700 prefixEnd_1038700 := by exact prefixLift 1038700
  have htrace : WordTrace (prefixWord ++ tailWord_1038700) baseStart_1038700 baseEnd_1038700 := by
    simpa [prefixWord, tailWord_1038700, baseEnd_1038700] using wordTrace_append hprefix tailTrace_1038700
  have hstable : (prefixWord ++ tailWord_1038700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038700).length < 2 ^ (prefixWord ++ tailWord_1038700).sum := by decide
  have hdescent : baseEnd_1038700 < baseStart_1038700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038706 : List Nat := [3, 2, 1, 2, 1, 3, 4, 2, 3]
def baseStart_1038706 : Nat := 118140960795 + 1038706 * 2 ^ 59
def prefixEnd_1038706 : Nat := 4983230072969 + 3 ^ 40 * 1038706 * 2
def baseEnd_1038706 : Nat := 237046860759608129643593

theorem tailTrace_1038706 : CollatzResearch.WordTrace tailWord_1038706 prefixEnd_1038706 237046860759608129643593 := by
  unfold tailWord_1038706
  simp only [CollatzResearch.WordTrace]
  refine ⟨9471180043738258426655993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25256480116635355804415981 9471180043738258426655993)
  ·
    refine ⟨7103385032803693819991995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9471180043738258426655993 7103385032803693819991995)
    ·
      refine ⟨10655077549205540729987993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7103385032803693819991995 10655077549205540729987993)
      ·
        refine ⟨7991308161904155547490995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10655077549205540729987993 7991308161904155547490995)
        ·
          refine ⟨11986962242856233321236493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7991308161904155547490995 11986962242856233321236493)
          ·
            refine ⟨4495110841071087495463685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11986962242856233321236493 4495110841071087495463685)
            ·
              refine ⟨842833282700828905399441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4495110841071087495463685 842833282700828905399441)
              ·
                refine ⟨632124962025621679049581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842833282700828905399441 632124962025621679049581)
                ·
                  refine ⟨237046860759608129643593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632124962025621679049581 237046860759608129643593)
                  ·
                    rfl

theorem cell21_1038706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_1038706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038706 prefixEnd_1038706 := by exact prefixLift 1038706
  have htrace : WordTrace (prefixWord ++ tailWord_1038706) baseStart_1038706 baseEnd_1038706 := by
    simpa [prefixWord, tailWord_1038706, baseEnd_1038706] using wordTrace_append hprefix tailTrace_1038706
  have hstable : (prefixWord ++ tailWord_1038706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038706).length < 2 ^ (prefixWord ++ tailWord_1038706).sum := by decide
  have hdescent : baseEnd_1038706 < baseStart_1038706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038717 : List Nat := [1, 4, 1, 1, 2, 3, 3, 6]
def baseStart_1038717 : Nat := 118140960795 + 1038717 * 2 ^ 59
def prefixEnd_1038717 : Nat := 4983230072969 + 3 ^ 40 * 1038717 * 2
def baseEnd_1038717 : Nat := 79016457036491518320079

theorem tailTrace_1038717 : CollatzResearch.WordTrace tailWord_1038717 prefixEnd_1038717 79016457036491518320079 := by
  unfold tailWord_1038717
  simp only [CollatzResearch.WordTrace]
  refine ⟨37885121377913182585274405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25256747585275455056849603 37885121377913182585274405)
  ·
    refine ⟨7103460258358721734738951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37885121377913182585274405 7103460258358721734738951)
    ·
      refine ⟨10655190387538082602108427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7103460258358721734738951 10655190387538082602108427)
      ·
        refine ⟨15982785581307123903162641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10655190387538082602108427 15982785581307123903162641)
        ·
          refine ⟨11987089185980342927371981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15982785581307123903162641 11987089185980342927371981)
          ·
            refine ⟨4495158444742628597764493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11987089185980342927371981 4495158444742628597764493)
            ·
              refine ⟨1685684416778485724161685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4495158444742628597764493 1685684416778485724161685)
              ·
                refine ⟨79016457036491518320079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1685684416778485724161685 79016457036491518320079)
                ·
                  rfl

theorem cell21_1038717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 6].length) (baseStart_1038717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038717 prefixEnd_1038717 := by exact prefixLift 1038717
  have htrace : WordTrace (prefixWord ++ tailWord_1038717) baseStart_1038717 baseEnd_1038717 := by
    simpa [prefixWord, tailWord_1038717, baseEnd_1038717] using wordTrace_append hprefix tailTrace_1038717
  have hstable : (prefixWord ++ tailWord_1038717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038717).length < 2 ^ (prefixWord ++ tailWord_1038717).sum := by decide
  have hdescent : baseEnd_1038717 < baseStart_1038717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038731 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 7]
def baseStart_1038731 : Nat := 118140960795 + 1038731 * 2 ^ 59
def prefixEnd_1038731 : Nat := 4983230072969 + 3 ^ 40 * 1038731 * 2
def baseEnd_1038731 : Nat := 237052566100213641726875

theorem tailTrace_1038731 : CollatzResearch.WordTrace tailWord_1038731 prefixEnd_1038731 237052566100213641726875 := by
  unfold tailWord_1038731
  simp only [CollatzResearch.WordTrace]
  refine ⟨37885631999862462976284047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25257087999908308650856031 37885631999862462976284047)
  ·
    refine ⟨56828447999793694464426071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37885631999862462976284047 56828447999793694464426071)
    ·
      refine ⟨85242671999690541696639107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56828447999793694464426071 85242671999690541696639107)
      ·
        refine ⟨127864007999535812544958661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85242671999690541696639107 127864007999535812544958661)
        ·
          refine ⟨23974501499912964852179749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127864007999535812544958661 23974501499912964852179749)
          ·
            refine ⟨4495219031233680909783703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23974501499912964852179749 4495219031233680909783703)
            ·
              refine ⟨6742828546850521364675555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4495219031233680909783703 6742828546850521364675555)
              ·
                refine ⟨10114242820275782047013333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6742828546850521364675555 10114242820275782047013333)
                ·
                  refine ⟨237052566100213641726875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10114242820275782047013333 237052566100213641726875)
                  ·
                    rfl

theorem cell21_1038731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 7].length) (baseStart_1038731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038731 prefixEnd_1038731 := by exact prefixLift 1038731
  have htrace : WordTrace (prefixWord ++ tailWord_1038731) baseStart_1038731 baseEnd_1038731 := by
    simpa [prefixWord, tailWord_1038731, baseEnd_1038731] using wordTrace_append hprefix tailTrace_1038731
  have hstable : (prefixWord ++ tailWord_1038731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038731).length < 2 ^ (prefixWord ++ tailWord_1038731).sum := by decide
  have hdescent : baseEnd_1038731 < baseStart_1038731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038776 : List Nat := [2, 1, 2, 1, 2, 2, 1, 10]
def baseStart_1038776 : Nat := 118140960795 + 1038776 * 2 ^ 59
def prefixEnd_1038776 : Nat := 4983230072969 + 3 ^ 40 * 1038776 * 2
def baseEnd_1038776 : Nat := 79020945237767854492261

theorem tailTrace_1038776 : CollatzResearch.WordTrace tailWord_1038776 prefixEnd_1038776 79020945237767854492261 := by
  unfold tailWord_1038776
  simp only [CollatzResearch.WordTrace]
  refine ⟨18943636642349717830836091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25258182189799623774448121 18943636642349717830836091)
  ·
    refine ⟨28415454963524576746254137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18943636642349717830836091 28415454963524576746254137)
    ·
      refine ⟨21311591222643432559690603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28415454963524576746254137 21311591222643432559690603)
      ·
        refine ⟨31967386833965148839535905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21311591222643432559690603 31967386833965148839535905)
        ·
          refine ⟨23975540125473861629651929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31967386833965148839535905 23975540125473861629651929)
          ·
            refine ⟨17981655094105396222238947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23975540125473861629651929 17981655094105396222238947)
            ·
              refine ⟨26972482641158094333358421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17981655094105396222238947 26972482641158094333358421)
              ·
                refine ⟨79020945237767854492261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26972482641158094333358421 79020945237767854492261)
                ·
                  rfl

theorem cell21_1038776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 10].length) (baseStart_1038776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038776 prefixEnd_1038776 := by exact prefixLift 1038776
  have htrace : WordTrace (prefixWord ++ tailWord_1038776) baseStart_1038776 baseEnd_1038776 := by
    simpa [prefixWord, tailWord_1038776, baseEnd_1038776] using wordTrace_append hprefix tailTrace_1038776
  have hstable : (prefixWord ++ tailWord_1038776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038776).length < 2 ^ (prefixWord ++ tailWord_1038776).sum := by decide
  have hdescent : baseEnd_1038776 < baseStart_1038776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038785 : List Nat := [1, 2, 7, 1, 1, 2, 2, 5]
def baseStart_1038785 : Nat := 118140960795 + 1038785 * 2 ^ 59
def prefixEnd_1038785 : Nat := 4983230072969 + 3 ^ 40 * 1038785 * 2
def baseEnd_1038785 : Nat := 79021629878640515942255

theorem tailTrace_1038785 : CollatzResearch.WordTrace tailWord_1038785 prefixEnd_1038785 79021629878640515942255 := by
  unfold tailWord_1038785
  simp only [CollatzResearch.WordTrace]
  refine ⟨37887601541666830198749809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25258401027777886799166539 37887601541666830198749809)
  ·
    refine ⟨28415701156250122649062357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37887601541666830198749809 28415701156250122649062357)
    ·
      refine ⟨665992995849612249587399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 28415701156250122649062357 665992995849612249587399)
      ·
        refine ⟨998989493774418374381099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665992995849612249587399 998989493774418374381099)
        ·
          refine ⟨1498484240661627561571649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998989493774418374381099 1498484240661627561571649)
          ·
            refine ⟨1123863180496220671178737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1498484240661627561571649 1123863180496220671178737)
            ·
              refine ⟨842897385372165503384053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1123863180496220671178737 842897385372165503384053)
              ·
                refine ⟨79021629878640515942255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 842897385372165503384053 79021629878640515942255)
                ·
                  rfl

theorem cell21_1038785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 5].length) (baseStart_1038785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038785 prefixEnd_1038785 := by exact prefixLift 1038785
  have htrace : WordTrace (prefixWord ++ tailWord_1038785) baseStart_1038785 baseEnd_1038785 := by
    simpa [prefixWord, tailWord_1038785, baseEnd_1038785] using wordTrace_append hprefix tailTrace_1038785
  have hstable : (prefixWord ++ tailWord_1038785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038785).length < 2 ^ (prefixWord ++ tailWord_1038785).sum := by decide
  have hdescent : baseEnd_1038785 < baseStart_1038785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038793 : List Nat := [1, 2, 1, 1, 2, 1, 8, 5]
def baseStart_1038793 : Nat := 118140960795 + 1038793 * 2 ^ 59
def prefixEnd_1038793 : Nat := 4983230072969 + 3 ^ 40 * 1038793 * 2
def baseEnd_1038793 : Nat := 79022238448305103897805

theorem tailTrace_1038793 : CollatzResearch.WordTrace tailWord_1038793 prefixEnd_1038793 79022238448305103897805 := by
  unfold tailWord_1038793
  simp only [CollatzResearch.WordTrace]
  refine ⟨37887893325637847565041033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25258595550425231710027355 37887893325637847565041033)
  ·
    refine ⟨28415919994228385673780775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37887893325637847565041033 28415919994228385673780775)
    ·
      refine ⟨42623879991342578510671163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28415919994228385673780775 42623879991342578510671163)
      ·
        refine ⟨63935819987013867766006745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42623879991342578510671163 63935819987013867766006745)
        ·
          refine ⟨47951864990260400824505059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63935819987013867766006745 47951864990260400824505059)
          ·
            refine ⟨71927797485390601236757589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47951864990260400824505059 71927797485390601236757589)
            ·
              refine ⟨842903876781921108243253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 71927797485390601236757589 842903876781921108243253)
              ·
                refine ⟨79022238448305103897805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 842903876781921108243253 79022238448305103897805)
                ·
                  rfl

theorem cell21_1038793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 5].length) (baseStart_1038793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038793 prefixEnd_1038793 := by exact prefixLift 1038793
  have htrace : WordTrace (prefixWord ++ tailWord_1038793) baseStart_1038793 baseEnd_1038793 := by
    simpa [prefixWord, tailWord_1038793, baseEnd_1038793] using wordTrace_append hprefix tailTrace_1038793
  have hstable : (prefixWord ++ tailWord_1038793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038793).length < 2 ^ (prefixWord ++ tailWord_1038793).sum := by decide
  have hdescent : baseEnd_1038793 < baseStart_1038793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038824 : List Nat := [2, 1, 4, 1, 1, 3, 3, 1, 5]
def baseStart_1038824 : Nat := 118140960795 + 1038824 * 2 ^ 59
def prefixEnd_1038824 : Nat := 4983230072969 + 3 ^ 40 * 1038824 * 2
def baseEnd_1038824 : Nat := 237073789967266146676685

theorem tailTrace_1038824 : CollatzResearch.WordTrace tailWord_1038824 prefixEnd_1038824 237073789967266146676685 := by
  unfold tailWord_1038824
  simp only [CollatzResearch.WordTrace]
  refine ⟨18944511994262769929709763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25259349325683693239613017 18944511994262769929709763)
  ·
    refine ⟨28416767991394154894564645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18944511994262769929709763 28416767991394154894564645)
    ·
      refine ⟨5328143998386404042730871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28416767991394154894564645 5328143998386404042730871)
      ·
        refine ⟨7992215997579606064096307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5328143998386404042730871 7992215997579606064096307)
        ·
          refine ⟨11988323996369409096144461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7992215997579606064096307 11988323996369409096144461)
          ·
            refine ⟨4495621498638528411054173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11988323996369409096144461 4495621498638528411054173)
            ·
              refine ⟨1685858061989448154145315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4495621498638528411054173 1685858061989448154145315)
              ·
                refine ⟨2528787092984172231217973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1685858061989448154145315 2528787092984172231217973)
                ·
                  refine ⟨237073789967266146676685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2528787092984172231217973 237073789967266146676685)
                  ·
                    rfl

theorem cell21_1038824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 5].length) (baseStart_1038824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038824 prefixEnd_1038824 := by exact prefixLift 1038824
  have htrace : WordTrace (prefixWord ++ tailWord_1038824) baseStart_1038824 baseEnd_1038824 := by
    simpa [prefixWord, tailWord_1038824, baseEnd_1038824] using wordTrace_append hprefix tailTrace_1038824
  have hstable : (prefixWord ++ tailWord_1038824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038824).length < 2 ^ (prefixWord ++ tailWord_1038824).sum := by decide
  have hdescent : baseEnd_1038824 < baseStart_1038824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038917 : List Nat := [1, 3, 1, 1, 1, 6, 2, 3, 3]
def baseStart_1038917 : Nat := 118140960795 + 1038917 * 2 ^ 59
def prefixEnd_1038917 : Nat := 4983230072969 + 3 ^ 40 * 1038917 * 2
def baseEnd_1038917 : Nat := 237095013834318651626495

theorem tailTrace_1038917 : CollatzResearch.WordTrace tailWord_1038917 prefixEnd_1038917 237095013834318651626495 := by
  unfold tailWord_1038917
  simp only [CollatzResearch.WordTrace]
  refine ⟨37892415977188616742555005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25261610651459077828370003 37892415977188616742555005)
  ·
    refine ⟨14209655991445731278458127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37892415977188616742555005 14209655991445731278458127)
    ·
      refine ⟨21314483987168596917687191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14209655991445731278458127 21314483987168596917687191)
      ·
        refine ⟨31971725980752895376530787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21314483987168596917687191 31971725980752895376530787)
        ·
          refine ⟨47957588971129343064796181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31971725980752895376530787 47957588971129343064796181)
          ·
            refine ⟨2248011983021687956162321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47957588971129343064796181 2248011983021687956162321)
            ·
              refine ⟨1686008987266265967121741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2248011983021687956162321 1686008987266265967121741)
              ·
                refine ⟨632253370224849737670653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1686008987266265967121741 632253370224849737670653)
                ·
                  refine ⟨237095013834318651626495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632253370224849737670653 237095013834318651626495)
                  ·
                    rfl

theorem cell21_1038917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_1038917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038917 prefixEnd_1038917 := by exact prefixLift 1038917
  have htrace : WordTrace (prefixWord ++ tailWord_1038917) baseStart_1038917 baseEnd_1038917 := by
    simpa [prefixWord, tailWord_1038917, baseEnd_1038917] using wordTrace_append hprefix tailTrace_1038917
  have hstable : (prefixWord ++ tailWord_1038917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038917).length < 2 ^ (prefixWord ++ tailWord_1038917).sum := by decide
  have hdescent : baseEnd_1038917 < baseStart_1038917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038959 : List Nat := [1, 1, 2, 1, 3, 2, 4, 2, 5]
def baseStart_1038959 : Nat := 118140960795 + 1038959 * 2 ^ 59
def prefixEnd_1038959 : Nat := 4983230072969 + 3 ^ 40 * 1038959 * 2
def baseEnd_1038959 : Nat := 237104598806535911926409

theorem tailTrace_1038959 : CollatzResearch.WordTrace tailWord_1038959 prefixEnd_1038959 237104598806535911926409 := by
  unfold tailWord_1038959
  simp only [CollatzResearch.WordTrace]
  refine ⟨37893947843036457915583931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25262631895357638610389287 37893947843036457915583931)
  ·
    refine ⟨56840921764554686873375897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37893947843036457915583931 56840921764554686873375897)
    ·
      refine ⟨42630691323416015155031923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56840921764554686873375897 42630691323416015155031923)
      ·
        refine ⟨63946036985124022732547885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42630691323416015155031923 63946036985124022732547885)
        ·
          refine ⟨23979763869421508524705457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63946036985124022732547885 23979763869421508524705457)
          ·
            refine ⟨17984822902066131393529093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23979763869421508524705457 17984822902066131393529093)
            ·
              refine ⟨3372154294137399636286705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17984822902066131393529093 3372154294137399636286705)
              ·
                refine ⟨2529115720603049727215029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3372154294137399636286705 2529115720603049727215029)
                ·
                  refine ⟨237104598806535911926409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2529115720603049727215029 237104598806535911926409)
                  ·
                    rfl

theorem cell21_1038959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 5].length) (baseStart_1038959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038959 prefixEnd_1038959 := by exact prefixLift 1038959
  have htrace : WordTrace (prefixWord ++ tailWord_1038959) baseStart_1038959 baseEnd_1038959 := by
    simpa [prefixWord, tailWord_1038959, baseEnd_1038959] using wordTrace_append hprefix tailTrace_1038959
  have hstable : (prefixWord ++ tailWord_1038959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038959).length < 2 ^ (prefixWord ++ tailWord_1038959).sum := by decide
  have hdescent : baseEnd_1038959 < baseStart_1038959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038990 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_1038990 : Nat := 118140960795 + 1038990 * 2 ^ 59
def prefixEnd_1038990 : Nat := 4983230072969 + 3 ^ 40 * 1038990 * 2
def baseEnd_1038990 : Nat := 237111673428886746909679

theorem tailTrace_1038990 : CollatzResearch.WordTrace tailWord_1038990 prefixEnd_1038990 237111673428886746909679 := by
  unfold tailWord_1038990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4736884813240518776245303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25263385670616100139974949 4736884813240518776245303)
  ·
    refine ⟨7105327219860778164367955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4736884813240518776245303 7105327219860778164367955)
    ·
      refine ⟨10657990829791167246551933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7105327219860778164367955 10657990829791167246551933)
      ·
        refine ⟨3996746561171687717456975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10657990829791167246551933 3996746561171687717456975)
        ·
          refine ⟨5995119841757531576185463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3996746561171687717456975 5995119841757531576185463)
          ·
            refine ⟨8992679762636297364278195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5995119841757531576185463 8992679762636297364278195)
            ·
              refine ⟨13489019643954446046417293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8992679762636297364278195 13489019643954446046417293)
              ·
                refine ⟨5058382366482917267406485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13489019643954446046417293 5058382366482917267406485)
                ·
                  refine ⟨237111673428886746909679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5058382366482917267406485 237111673428886746909679)
                  ·
                    rfl

theorem cell21_1038990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_1038990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1038990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1038990 prefixEnd_1038990 := by exact prefixLift 1038990
  have htrace : WordTrace (prefixWord ++ tailWord_1038990) baseStart_1038990 baseEnd_1038990 := by
    simpa [prefixWord, tailWord_1038990, baseEnd_1038990] using wordTrace_append hprefix tailTrace_1038990
  have hstable : (prefixWord ++ tailWord_1038990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038990).length < 2 ^ (prefixWord ++ tailWord_1038990).sum := by decide
  have hdescent : baseEnd_1038990 < baseStart_1038990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039021 : List Nat := [1, 5, 2, 1, 1, 2, 2, 7]
def baseStart_1039021 : Nat := 118140960795 + 1039021 * 2 ^ 59
def prefixEnd_1039021 : Nat := 4983230072969 + 3 ^ 40 * 1039021 * 2
def baseEnd_1039021 : Nat := 79039582683745860630983

theorem tailTrace_1039021 : CollatzResearch.WordTrace tailWord_1039021 prefixEnd_1039021 79039582683745860630983 := by
  unfold tailWord_1039021
  simp only [CollatzResearch.WordTrace]
  refine ⟨37896209168811842504340917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25264139445874561669560611 37896209168811842504340917)
  ·
    refine ⟨3552769609576110234781961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37896209168811842504340917 3552769609576110234781961)
    ·
      refine ⟨2664577207182082676086471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3552769609576110234781961 2664577207182082676086471)
      ·
        refine ⟨3996865810773124014129707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2664577207182082676086471 3996865810773124014129707)
        ·
          refine ⟨5995298716159686021194561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3996865810773124014129707 5995298716159686021194561)
          ·
            refine ⟨4496474037119764515895921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5995298716159686021194561 4496474037119764515895921)
            ·
              refine ⟨3372355527839823386921941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4496474037119764515895921 3372355527839823386921941)
              ·
                refine ⟨79039582683745860630983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3372355527839823386921941 79039582683745860630983)
                ·
                  rfl

theorem cell21_1039021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 7].length) (baseStart_1039021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1039021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1039021 prefixEnd_1039021 := by exact prefixLift 1039021
  have htrace : WordTrace (prefixWord ++ tailWord_1039021) baseStart_1039021 baseEnd_1039021 := by
    simpa [prefixWord, tailWord_1039021, baseEnd_1039021] using wordTrace_append hprefix tailTrace_1039021
  have hstable : (prefixWord ++ tailWord_1039021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039021).length < 2 ^ (prefixWord ++ tailWord_1039021).sum := by decide
  have hdescent : baseEnd_1039021 < baseStart_1039021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039041 : List Nat := [1, 2, 6, 2, 1, 1, 2, 2, 4]
def baseStart_1039041 : Nat := 118140960795 + 1039041 * 2 ^ 59
def prefixEnd_1039041 : Nat := 4983230072969 + 3 ^ 40 * 1039041 * 2
def baseEnd_1039041 : Nat := 237123312323721991559575

theorem tailTrace_1039041 : CollatzResearch.WordTrace tailWord_1039041 prefixEnd_1039041 237123312323721991559575 := by
  unfold tailWord_1039041
  simp only [CollatzResearch.WordTrace]
  refine ⟨37896938628739385920068977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25264625752492923946712651 37896938628739385920068977)
  ·
    refine ⟨28422703971554539440051733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37896938628739385920068977 28422703971554539440051733)
    ·
      refine ⟨1332314248666619036252425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28422703971554539440051733 1332314248666619036252425)
      ·
        refine ⟨999235686499964277189319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1332314248666619036252425 999235686499964277189319)
        ·
          refine ⟨1498853529749946415783979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 999235686499964277189319 1498853529749946415783979)
          ·
            refine ⟨2248280294624919623675969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1498853529749946415783979 2248280294624919623675969)
            ·
              refine ⟨1686210220968689717756977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2248280294624919623675969 1686210220968689717756977)
              ·
                refine ⟨1264657665726517288317733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1686210220968689717756977 1264657665726517288317733)
                ·
                  refine ⟨237123312323721991559575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1264657665726517288317733 237123312323721991559575)
                  ·
                    rfl

theorem cell21_1039041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 4].length) (baseStart_1039041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1039041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1039041 prefixEnd_1039041 := by exact prefixLift 1039041
  have htrace : WordTrace (prefixWord ++ tailWord_1039041) baseStart_1039041 baseEnd_1039041 := by
    simpa [prefixWord, tailWord_1039041, baseEnd_1039041] using wordTrace_append hprefix tailTrace_1039041
  have hstable : (prefixWord ++ tailWord_1039041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039041).length < 2 ^ (prefixWord ++ tailWord_1039041).sum := by decide
  have hdescent : baseEnd_1039041 < baseStart_1039041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039066 : List Nat := [3, 1, 1, 2, 2, 2, 1, 5, 4]
def baseStart_1039066 : Nat := 118140960795 + 1039066 * 2 ^ 59
def prefixEnd_1039066 : Nat := 4983230072969 + 3 ^ 40 * 1039066 * 2
def baseEnd_1039066 : Nat := 237129017664327503642857

theorem tailTrace_1039066 : CollatzResearch.WordTrace tailWord_1039066 prefixEnd_1039066 237129017664327503642857 := by
  unfold tailWord_1039066
  simp only [CollatzResearch.WordTrace]
  refine ⟨9474462613412203797432263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25265233635765876793152701 9474462613412203797432263)
  ·
    refine ⟨14211693920118305696148395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9474462613412203797432263 14211693920118305696148395)
    ·
      refine ⟨21317540880177458544222593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14211693920118305696148395 21317540880177458544222593)
      ·
        refine ⟨15988155660133093908166945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21317540880177458544222593 15988155660133093908166945)
        ·
          refine ⟨11991116745099820431125209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15988155660133093908166945 11991116745099820431125209)
          ·
            refine ⟨8993337558824865323343907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11991116745099820431125209 8993337558824865323343907)
            ·
              refine ⟨13490006338237297985015861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8993337558824865323343907 13490006338237297985015861)
              ·
                refine ⟨1264688094209746686095237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13490006338237297985015861 1264688094209746686095237)
                ·
                  refine ⟨237129017664327503642857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1264688094209746686095237 237129017664327503642857)
                  ·
                    rfl

theorem cell21_1039066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_1039066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1039066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1039066 prefixEnd_1039066 := by exact prefixLift 1039066
  have htrace : WordTrace (prefixWord ++ tailWord_1039066) baseStart_1039066 baseEnd_1039066 := by
    simpa [prefixWord, tailWord_1039066, baseEnd_1039066] using wordTrace_append hprefix tailTrace_1039066
  have hstable : (prefixWord ++ tailWord_1039066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039066).length < 2 ^ (prefixWord ++ tailWord_1039066).sum := by decide
  have hdescent : baseEnd_1039066 < baseStart_1039066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039162 : List Nat := [3, 1, 1, 1, 6, 1, 3, 2, 3]
def baseStart_1039162 : Nat := 118140960795 + 1039162 * 2 ^ 59
def prefixEnd_1039162 : Nat := 4983230072969 + 3 ^ 40 * 1039162 * 2
def baseEnd_1039162 : Nat := 237150926172252670042661

theorem tailTrace_1039162 : CollatzResearch.WordTrace tailWord_1039162 prefixEnd_1039162 237150926172252670042661 := by
  unfold tailWord_1039162
  simp only [CollatzResearch.WordTrace]
  refine ⟨9475337965325255896305935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25267567907534015723482493 9475337965325255896305935)
  ·
    refine ⟨14213006947987883844458903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9475337965325255896305935 14213006947987883844458903)
    ·
      refine ⟨21319510421981825766688355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14213006947987883844458903 21319510421981825766688355)
      ·
        refine ⟨31979265632972738650032533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21319510421981825766688355 31979265632972738650032533)
        ·
          refine ⟨1499028076545597124220275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31979265632972738650032533 1499028076545597124220275)
          ·
            refine ⟨2248542114818395686330413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499028076545597124220275 2248542114818395686330413)
            ·
              refine ⟨843203293056898382373905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2248542114818395686330413 843203293056898382373905)
              ·
                refine ⟨632402469792673786780429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 843203293056898382373905 632402469792673786780429)
                ·
                  refine ⟨237150926172252670042661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632402469792673786780429 237150926172252670042661)
                  ·
                    rfl

theorem cell21_1039162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_1039162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1039162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1039162 prefixEnd_1039162 := by exact prefixLift 1039162
  have htrace : WordTrace (prefixWord ++ tailWord_1039162) baseStart_1039162 baseEnd_1039162 := by
    simpa [prefixWord, tailWord_1039162, baseEnd_1039162] using wordTrace_append hprefix tailTrace_1039162
  have hstable : (prefixWord ++ tailWord_1039162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039162).length < 2 ^ (prefixWord ++ tailWord_1039162).sum := by decide
  have hdescent : baseEnd_1039162 < baseStart_1039162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039201 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 6]
def baseStart_1039201 : Nat := 118140960795 + 1039201 * 2 ^ 59
def prefixEnd_1039201 : Nat := 4983230072969 + 3 ^ 40 * 1039201 * 2
def baseEnd_1039201 : Nat := 237159826503597268892581

theorem tailTrace_1039201 : CollatzResearch.WordTrace tailWord_1039201 prefixEnd_1039201 237159826503597268892581 := by
  unfold tailWord_1039201
  simp only [CollatzResearch.WordTrace]
  refine ⟨37902774308159733245893457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25268516205439822163928971 37902774308159733245893457)
  ·
    refine ⟨28427080731119799934420093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37902774308159733245893457 28427080731119799934420093)
    ·
      refine ⟨10660155274169924975407535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28427080731119799934420093 10660155274169924975407535)
      ·
        refine ⟨15990232911254887463111303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10660155274169924975407535 15990232911254887463111303)
        ·
          refine ⟨23985349366882331194666955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15990232911254887463111303 23985349366882331194666955)
          ·
            refine ⟨35978024050323496792000433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23985349366882331194666955 35978024050323496792000433)
            ·
              refine ⟨26983518037742622594000325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35978024050323496792000433 26983518037742622594000325)
              ·
                refine ⟨5059409632076741736375061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26983518037742622594000325 5059409632076741736375061)
                ·
                  refine ⟨237159826503597268892581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5059409632076741736375061 237159826503597268892581)
                  ·
                    rfl

theorem cell21_1039201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_1039201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1039201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1039201 prefixEnd_1039201 := by exact prefixLift 1039201
  have htrace : WordTrace (prefixWord ++ tailWord_1039201) baseStart_1039201 baseEnd_1039201 := by
    simpa [prefixWord, tailWord_1039201, baseEnd_1039201] using wordTrace_append hprefix tailTrace_1039201
  have hstable : (prefixWord ++ tailWord_1039201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039201).length < 2 ^ (prefixWord ++ tailWord_1039201).sum := by decide
  have hdescent : baseEnd_1039201 < baseStart_1039201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039218 : List Nat := [3, 2, 1, 2, 1, 1, 3, 4, 4]
def baseStart_1039218 : Nat := 118140960795 + 1039218 * 2 ^ 59
def prefixEnd_1039218 : Nat := 4983230072969 + 3 ^ 40 * 1039218 * 2
def baseEnd_1039218 : Nat := 237163706135209017109213

theorem tailTrace_1039218 : CollatzResearch.WordTrace tailWord_1039218 prefixEnd_1039218 237163706135209017109213 := by
  unfold tailWord_1039218
  simp only [CollatzResearch.WordTrace]
  refine ⟨9475848587274536287315577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25268929566065430099508205 9475848587274536287315577)
  ·
    refine ⟨7106886440455902215486683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9475848587274536287315577 7106886440455902215486683)
    ·
      refine ⟨10660329660683853323230025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7106886440455902215486683 10660329660683853323230025)
      ·
        refine ⟨7995247245512889992422519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10660329660683853323230025 7995247245512889992422519)
        ·
          refine ⟨11992870868269334988633779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7995247245512889992422519 11992870868269334988633779)
          ·
            refine ⟨17989306302404002482950669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11992870868269334988633779 17989306302404002482950669)
            ·
              refine ⟨6745989863401500931106501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17989306302404002482950669 6745989863401500931106501)
              ·
                refine ⟨1264873099387781424582469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6745989863401500931106501 1264873099387781424582469)
                ·
                  refine ⟨237163706135209017109213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1264873099387781424582469 237163706135209017109213)
                  ·
                    rfl

theorem cell21_1039218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_1039218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1039218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1039218 prefixEnd_1039218 := by exact prefixLift 1039218
  have htrace : WordTrace (prefixWord ++ tailWord_1039218) baseStart_1039218 baseEnd_1039218 := by
    simpa [prefixWord, tailWord_1039218, baseEnd_1039218] using wordTrace_append hprefix tailTrace_1039218
  have hstable : (prefixWord ++ tailWord_1039218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039218).length < 2 ^ (prefixWord ++ tailWord_1039218).sum := by decide
  have hdescent : baseEnd_1039218 < baseStart_1039218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039221 : List Nat := [1, 3, 4, 1, 1, 3, 1, 4, 3]
def baseStart_1039221 : Nat := 118140960795 + 1039221 * 2 ^ 59
def prefixEnd_1039221 : Nat := 4983230072969 + 3 ^ 40 * 1039221 * 2
def baseEnd_1039221 : Nat := 237164390776081678559207

theorem tailTrace_1039221 : CollatzResearch.WordTrace tailWord_1039221 prefixEnd_1039221 237164390776081678559207 := by
  unfold tailWord_1039221
  simp only [CollatzResearch.WordTrace]
  refine ⟨37903503768087276661621517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25269002512058184441081011 37903503768087276661621517)
  ·
    refine ⟨14213813913032728748108069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37903503768087276661621517 14213813913032728748108069)
    ·
      refine ⟨2665090108693636640270263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14213813913032728748108069 2665090108693636640270263)
      ·
        refine ⟨3997635163040454960405395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2665090108693636640270263 3997635163040454960405395)
        ·
          refine ⟨5996452744560682440608093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3997635163040454960405395 5996452744560682440608093)
          ·
            refine ⟨2248669779210255915228035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5996452744560682440608093 2248669779210255915228035)
            ·
              refine ⟨3373004668815383872842053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2248669779210255915228035 3373004668815383872842053)
              ·
                refine ⟨632438375402884476157885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3373004668815383872842053 632438375402884476157885)
                ·
                  refine ⟨237164390776081678559207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632438375402884476157885 237164390776081678559207)
                  ·
                    rfl

theorem cell21_1039221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_1039221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1039221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1039221 prefixEnd_1039221 := by exact prefixLift 1039221
  have htrace : WordTrace (prefixWord ++ tailWord_1039221) baseStart_1039221 baseEnd_1039221 := by
    simpa [prefixWord, tailWord_1039221, baseEnd_1039221] using wordTrace_append hprefix tailTrace_1039221
  have hstable : (prefixWord ++ tailWord_1039221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039221).length < 2 ^ (prefixWord ++ tailWord_1039221).sum := by decide
  have hdescent : baseEnd_1039221 < baseStart_1039221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039300 : List Nat := [2, 3, 3, 3, 2, 1, 2, 5]
def baseStart_1039300 : Nat := 118140960795 + 1039300 * 2 ^ 59
def prefixEnd_1039300 : Nat := 4983230072969 + 3 ^ 40 * 1039300 * 2
def baseEnd_1039300 : Nat := 79060806550798365580793

theorem tailTrace_1039300 : CollatzResearch.WordTrace tailWord_1039300 prefixEnd_1039300 79060806550798365580793 := by
  unfold tailWord_1039300
  simp only [CollatzResearch.WordTrace]
  refine ⟨18953192567400536576873677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25270923423200715435831569 18953192567400536576873677)
  ·
    refine ⟨7107447212775201216327629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18953192567400536576873677 7107447212775201216327629)
    ·
      refine ⟨2665292704790700456122861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7107447212775201216327629 2665292704790700456122861)
      ·
        refine ⟨999484764296512671046073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2665292704790700456122861 999484764296512671046073)
        ·
          refine ⟨749613573222384503284555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 999484764296512671046073 749613573222384503284555)
          ·
            refine ⟨1124420359833576754926833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749613573222384503284555 1124420359833576754926833)
            ·
              refine ⟨843315269875182566195125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1124420359833576754926833 843315269875182566195125)
              ·
                refine ⟨79060806550798365580793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 843315269875182566195125 79060806550798365580793)
                ·
                  rfl

theorem cell21_1039300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 5].length) (baseStart_1039300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1039300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1039300 prefixEnd_1039300 := by exact prefixLift 1039300
  have htrace : WordTrace (prefixWord ++ tailWord_1039300) baseStart_1039300 baseEnd_1039300 := by
    simpa [prefixWord, tailWord_1039300, baseEnd_1039300] using wordTrace_append hprefix tailTrace_1039300
  have hstable : (prefixWord ++ tailWord_1039300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039300).length < 2 ^ (prefixWord ++ tailWord_1039300).sum := by decide
  have hdescent : baseEnd_1039300 < baseStart_1039300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039308 : List Nat := [2, 2, 1, 4, 1, 1, 3, 7]
def baseStart_1039308 : Nat := 118140960795 + 1039308 * 2 ^ 59
def prefixEnd_1039308 : Nat := 4983230072969 + 3 ^ 40 * 1039308 * 2
def baseEnd_1039308 : Nat := 79061415120462953536343

theorem tailTrace_1039308 : CollatzResearch.WordTrace tailWord_1039308 prefixEnd_1039308 79061415120462953536343 := by
  unfold tailWord_1039308
  simp only [CollatzResearch.WordTrace]
  refine ⟨18953338459386045260019289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25271117945848060346692385 18953338459386045260019289)
  ·
    refine ⟨14215003844539533945014467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18953338459386045260019289 14215003844539533945014467)
    ·
      refine ⟨21322505766809300917521701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14215003844539533945014467 21322505766809300917521701)
      ·
        refine ⟨3997969831276743922035319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21322505766809300917521701 3997969831276743922035319)
        ·
          refine ⟨5996954746915115883052979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3997969831276743922035319 5996954746915115883052979)
          ·
            refine ⟨8995432120372673824579469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5996954746915115883052979 8995432120372673824579469)
            ·
              refine ⟨3373287045139752684217301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8995432120372673824579469 3373287045139752684217301)
              ·
                refine ⟨79061415120462953536343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3373287045139752684217301 79061415120462953536343)
                ·
                  rfl

theorem cell21_1039308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 7].length) (baseStart_1039308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1039308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1039308 prefixEnd_1039308 := by exact prefixLift 1039308
  have htrace : WordTrace (prefixWord ++ tailWord_1039308) baseStart_1039308 baseEnd_1039308 := by
    simpa [prefixWord, tailWord_1039308, baseEnd_1039308] using wordTrace_append hprefix tailTrace_1039308
  have hstable : (prefixWord ++ tailWord_1039308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039308).length < 2 ^ (prefixWord ++ tailWord_1039308).sum := by decide
  have hdescent : baseEnd_1039308 < baseStart_1039308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039314 : List Nat := [3, 2, 2, 3, 1, 3, 1, 3, 3]
def baseStart_1039314 : Nat := 118140960795 + 1039314 * 2 ^ 59
def prefixEnd_1039314 : Nat := 4983230072969 + 3 ^ 40 * 1039314 * 2
def baseEnd_1039314 : Nat := 237185614643134183509017

theorem tailTrace_1039314 : CollatzResearch.WordTrace tailWord_1039314 prefixEnd_1039314 237185614643134183509017 := by
  unfold tailWord_1039314
  simp only [CollatzResearch.WordTrace]
  refine ⟨9476723939187588386189249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25271263837833569029837997 9476723939187588386189249)
  ·
    refine ⟨7107542954390691289641937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9476723939187588386189249 7107542954390691289641937)
    ·
      refine ⟨5330657215793018467231453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7107542954390691289641937 5330657215793018467231453)
      ·
        refine ⟨1998996455922381925211795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5330657215793018467231453 1998996455922381925211795)
        ·
          refine ⟨2998494683883572887817693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1998996455922381925211795 2998494683883572887817693)
          ·
            refine ⟨1124435506456339832931635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2998494683883572887817693 1124435506456339832931635)
            ·
              refine ⟨1686653259684509749397453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124435506456339832931635 1686653259684509749397453)
              ·
                refine ⟨632494972381691156024045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1686653259684509749397453 632494972381691156024045)
                ·
                  refine ⟨237185614643134183509017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632494972381691156024045 237185614643134183509017)
                  ·
                    rfl

theorem cell21_1039314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_1039314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1039314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1039314 prefixEnd_1039314 := by exact prefixLift 1039314
  have htrace : WordTrace (prefixWord ++ tailWord_1039314) baseStart_1039314 baseEnd_1039314 := by
    simpa [prefixWord, tailWord_1039314, baseEnd_1039314] using wordTrace_append hprefix tailTrace_1039314
  have hstable : (prefixWord ++ tailWord_1039314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039314).length < 2 ^ (prefixWord ++ tailWord_1039314).sum := by decide
  have hdescent : baseEnd_1039314 < baseStart_1039314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039325 : List Nat := [1, 4, 3, 1, 2, 3, 7]
def baseStart_1039325 : Nat := 118140960795 + 1039325 * 2 ^ 59
def prefixEnd_1039325 : Nat := 4983230072969 + 3 ^ 40 * 1039325 * 2
def baseEnd_1039325 : Nat := 26354236110333400980629

theorem tailTrace_1039325 : CollatzResearch.WordTrace tailWord_1039325 prefixEnd_1039325 26354236110333400980629 := by
  unfold tailWord_1039325
  simp only [CollatzResearch.WordTrace]
  refine ⟨37907296959710502423407429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25271531306473668282271619 37907296959710502423407429)
  ·
    refine ⟨7107618179945719204388893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37907296959710502423407429 7107618179945719204388893)
    ·
      refine ⟨2665356817479644701645835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7107618179945719204388893 2665356817479644701645835)
      ·
        refine ⟨3998035226219467052468753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2665356817479644701645835 3998035226219467052468753)
        ·
          refine ⟨2998526419664600289351565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3998035226219467052468753 2998526419664600289351565)
          ·
            refine ⟨1124447407374225108506837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2998526419664600289351565 1124447407374225108506837)
            ·
              refine ⟨26354236110333400980629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1124447407374225108506837 26354236110333400980629)
              ·
                rfl

theorem cell21_1039325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 7].length) (baseStart_1039325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1039325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1039325 prefixEnd_1039325 := by exact prefixLift 1039325
  have htrace : WordTrace (prefixWord ++ tailWord_1039325) baseStart_1039325 baseEnd_1039325 := by
    simpa [prefixWord, tailWord_1039325, baseEnd_1039325] using wordTrace_append hprefix tailTrace_1039325
  have hstable : (prefixWord ++ tailWord_1039325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039325).length < 2 ^ (prefixWord ++ tailWord_1039325).sum := by decide
  have hdescent : baseEnd_1039325 < baseStart_1039325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039432 : List Nat := [2, 1, 3, 1, 1, 1, 6, 3, 3]
def baseStart_1039432 : Nat := 118140960795 + 1039432 * 2 ^ 59
def prefixEnd_1039432 : Nat := 4983230072969 + 3 ^ 40 * 1039432 * 2
def baseEnd_1039432 : Nat := 237212543850792200542109

theorem tailTrace_1039432 : CollatzResearch.WordTrace tailWord_1039432 prefixEnd_1039432 237212543850792200542109 := by
  unfold tailWord_1039432
  simp only [CollatzResearch.WordTrace]
  refine ⟨18955599785161429848776275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25274133046881906465035033 18955599785161429848776275)
  ·
    refine ⟨28433399677742144773164413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18955599785161429848776275 28433399677742144773164413)
    ·
      refine ⟨10662524879153304289936655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28433399677742144773164413 10662524879153304289936655)
      ·
        refine ⟨15993787318729956434904983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10662524879153304289936655 15993787318729956434904983)
        ·
          refine ⟨23990680978094934652357475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15993787318729956434904983 23990680978094934652357475)
          ·
            refine ⟨35986021467142401978536213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23990680978094934652357475 35986021467142401978536213)
            ·
              refine ⟨1686844756272300092743885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35986021467142401978536213 1686844756272300092743885)
              ·
                refine ⟨632566783602112534778957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1686844756272300092743885 632566783602112534778957)
                ·
                  refine ⟨237212543850792200542109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632566783602112534778957 237212543850792200542109)
                  ·
                    rfl

theorem cell21_1039432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 3].length) (baseStart_1039432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1039432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1039432 prefixEnd_1039432 := by exact prefixLift 1039432
  have htrace : WordTrace (prefixWord ++ tailWord_1039432) baseStart_1039432 baseEnd_1039432 := by
    simpa [prefixWord, tailWord_1039432, baseEnd_1039432] using wordTrace_append hprefix tailTrace_1039432
  have hstable : (prefixWord ++ tailWord_1039432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039432).length < 2 ^ (prefixWord ++ tailWord_1039432).sum := by decide
  have hdescent : baseEnd_1039432 < baseStart_1039432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039463 : List Nat := [1, 1, 5, 1, 1, 4, 3, 1, 4]
def baseStart_1039463 : Nat := 118140960795 + 1039463 * 2 ^ 59
def prefixEnd_1039463 : Nat := 4983230072969 + 3 ^ 40 * 1039463 * 2
def baseEnd_1039463 : Nat := 237219618473143035525379

theorem tailTrace_1039463 : CollatzResearch.WordTrace tailWord_1039463 prefixEnd_1039463 237219618473143035525379 := by
  unfold tailWord_1039463
  simp only [CollatzResearch.WordTrace]
  refine ⟨37912330233210551991931043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25274886822140367994620695 37912330233210551991931043)
  ·
    refine ⟨56868495349815827987896565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37912330233210551991931043 56868495349815827987896565)
    ·
      refine ⟨5331421439045233873865303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56868495349815827987896565 5331421439045233873865303)
      ·
        refine ⟨7997132158567850810797955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5331421439045233873865303 7997132158567850810797955)
        ·
          refine ⟨11995698237851776216196933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7997132158567850810797955 11995698237851776216196933)
          ·
            refine ⟨2249193419597208040536925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11995698237851776216196933 2249193419597208040536925)
            ·
              refine ⟨843447532348953015201347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2249193419597208040536925 843447532348953015201347)
              ·
                refine ⟨1265171298523429522802021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 843447532348953015201347 1265171298523429522802021)
                ·
                  refine ⟨237219618473143035525379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1265171298523429522802021 237219618473143035525379)
                  ·
                    rfl

theorem cell21_1039463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 4].length) (baseStart_1039463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1039463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1039463 prefixEnd_1039463 := by exact prefixLift 1039463
  have htrace : WordTrace (prefixWord ++ tailWord_1039463) baseStart_1039463 baseEnd_1039463 := by
    simpa [prefixWord, tailWord_1039463, baseEnd_1039463] using wordTrace_append hprefix tailTrace_1039463
  have hstable : (prefixWord ++ tailWord_1039463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039463).length < 2 ^ (prefixWord ++ tailWord_1039463).sum := by decide
  have hdescent : baseEnd_1039463 < baseStart_1039463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039612 : List Nat := [2, 2, 2, 1, 5, 1, 8]
def baseStart_1039612 : Nat := 118140960795 + 1039612 * 2 ^ 59
def prefixEnd_1039612 : Nat := 4983230072969 + 3 ^ 40 * 1039612 * 2
def baseEnd_1039612 : Nat := 26361513589239098615749

theorem tailTrace_1039612 : CollatzResearch.WordTrace tailWord_1039612 prefixEnd_1039612 26361513589239098615749 := by
  unfold tailWord_1039612
  simp only [CollatzResearch.WordTrace]
  refine ⟨18958882354835375219552545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25278509806447166959403393 18958882354835375219552545)
  ·
    refine ⟨14219161766126531414664409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18958882354835375219552545 14219161766126531414664409)
    ·
      refine ⟨10664371324594898560998307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14219161766126531414664409 10664371324594898560998307)
      ·
        refine ⟨15996556986892347841497461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10664371324594898560998307 15996556986892347841497461)
        ·
          refine ⟨1499677217521157610140387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15996556986892347841497461 1499677217521157610140387)
          ·
            refine ⟨2249515826281736415210581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499677217521157610140387 2249515826281736415210581)
            ·
              refine ⟨26361513589239098615749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2249515826281736415210581 26361513589239098615749)
              ·
                rfl

theorem cell21_1039612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 8].length) (baseStart_1039612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1039612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1039612 prefixEnd_1039612 := by exact prefixLift 1039612
  have htrace : WordTrace (prefixWord ++ tailWord_1039612) baseStart_1039612 baseEnd_1039612 := by
    simpa [prefixWord, tailWord_1039612, baseEnd_1039612] using wordTrace_append hprefix tailTrace_1039612
  have hstable : (prefixWord ++ tailWord_1039612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039612).length < 2 ^ (prefixWord ++ tailWord_1039612).sum := by decide
  have hdescent : baseEnd_1039612 < baseStart_1039612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039646 : List Nat := [4, 3, 2, 1, 2, 1, 1, 7]
def baseStart_1039646 : Nat := 118140960795 + 1039646 * 2 ^ 59
def prefixEnd_1039646 : Nat := 4983230072969 + 3 ^ 40 * 1039646 * 2
def baseEnd_1039646 : Nat := 79087127188791794658335

theorem tailTrace_1039646 : CollatzResearch.WordTrace tailWord_1039646 prefixEnd_1039646 79087127188791794658335 := by
  unfold tailWord_1039646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4739875598943446780730349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25279336527698382830561861 4739875598943446780730349)
  ·
    refine ⟨1777453349603792542773881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4739875598943446780730349 1777453349603792542773881)
    ·
      refine ⟨1333090012202844407080411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1777453349603792542773881 1333090012202844407080411)
      ·
        refine ⟨1999635018304266610620617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1333090012202844407080411 1999635018304266610620617)
        ·
          refine ⟨1499726263728199957965463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1999635018304266610620617 1499726263728199957965463)
          ·
            refine ⟨2249589395592299936948195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499726263728199957965463 2249589395592299936948195)
            ·
              refine ⟨3374384093388449905422293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2249589395592299936948195 3374384093388449905422293)
              ·
                refine ⟨79087127188791794658335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3374384093388449905422293 79087127188791794658335)
                ·
                  rfl

theorem cell21_1039646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_1039646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1039646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1039646 prefixEnd_1039646 := by exact prefixLift 1039646
  have htrace : WordTrace (prefixWord ++ tailWord_1039646) baseStart_1039646 baseEnd_1039646 := by
    simpa [prefixWord, tailWord_1039646, baseEnd_1039646] using wordTrace_append hprefix tailTrace_1039646
  have hstable : (prefixWord ++ tailWord_1039646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039646).length < 2 ^ (prefixWord ++ tailWord_1039646).sum := by decide
  have hdescent : baseEnd_1039646 < baseStart_1039646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039677 : List Nat := [1, 4, 1, 5, 1, 2, 1, 1, 5]
def baseStart_1039677 : Nat := 118140960795 + 1039677 * 2 ^ 59
def prefixEnd_1039677 : Nat := 4983230072969 + 3 ^ 40 * 1039677 * 2
def baseEnd_1039677 : Nat := 237268456188726218958275

theorem tailTrace_1039677 : CollatzResearch.WordTrace tailWord_1039677 prefixEnd_1039677 237268456188726218958275 := by
  unfold tailWord_1039677
  simp only [CollatzResearch.WordTrace]
  refine ⟨37920135454435266540221285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25280090302956844360147523 37920135454435266540221285)
  ·
    refine ⟨7110025397706612476291491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37920135454435266540221285 7110025397706612476291491)
    ·
      refine ⟨10665038096559918714437237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7110025397706612476291491 10665038096559918714437237)
      ·
        refine ⟨999847321552492379478491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10665038096559918714437237 999847321552492379478491)
        ·
          refine ⟨1499770982328738569217737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 999847321552492379478491 1499770982328738569217737)
          ·
            refine ⟨1124828236746553926913303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1499770982328738569217737 1124828236746553926913303)
            ·
              refine ⟨1687242355119830890369955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124828236746553926913303 1687242355119830890369955)
              ·
                refine ⟨2530863532679746335554933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1687242355119830890369955 2530863532679746335554933)
                ·
                  refine ⟨237268456188726218958275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2530863532679746335554933 237268456188726218958275)
                  ·
                    rfl

theorem cell21_1039677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_1039677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1039677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1039677 prefixEnd_1039677 := by exact prefixLift 1039677
  have htrace : WordTrace (prefixWord ++ tailWord_1039677) baseStart_1039677 baseEnd_1039677 := by
    simpa [prefixWord, tailWord_1039677, baseEnd_1039677] using wordTrace_append hprefix tailTrace_1039677
  have hstable : (prefixWord ++ tailWord_1039677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039677).length < 2 ^ (prefixWord ++ tailWord_1039677).sum := by decide
  have hdescent : baseEnd_1039677 < baseStart_1039677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039784 : List Nat := [2, 1, 6, 1, 2, 2, 1, 2, 4]
def baseStart_1039784 : Nat := 118140960795 + 1039784 * 2 ^ 59
def prefixEnd_1039784 : Nat := 4983230072969 + 3 ^ 40 * 1039784 * 2
def baseEnd_1039784 : Nat := 237292875046517810674723

theorem tailTrace_1039784 : CollatzResearch.WordTrace tailWord_1039784 prefixEnd_1039784 237292875046517810674723 := by
  unfold tailWord_1039784
  simp only [CollatzResearch.WordTrace]
  refine ⟨18962019032523811907183203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25282692043365082542910937 18962019032523811907183203)
  ·
    refine ⟨28443028548785717860774805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18962019032523811907183203 28443028548785717860774805)
    ·
      refine ⟨1333266963224330524723819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28443028548785717860774805 1333266963224330524723819)
      ·
        refine ⟨1999900444836495787085729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1333266963224330524723819 1999900444836495787085729)
        ·
          refine ⟨1499925333627371840314297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1999900444836495787085729 1499925333627371840314297)
          ·
            refine ⟨1124944000220528880235723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1499925333627371840314297 1124944000220528880235723)
            ·
              refine ⟨1687416000330793320353585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124944000220528880235723 1687416000330793320353585)
              ·
                refine ⟨1265562000248094990265189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1687416000330793320353585 1265562000248094990265189)
                ·
                  refine ⟨237292875046517810674723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1265562000248094990265189 237292875046517810674723)
                  ·
                    rfl

theorem cell21_1039784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 4].length) (baseStart_1039784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1039784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1039784 prefixEnd_1039784 := by exact prefixLift 1039784
  have htrace : WordTrace (prefixWord ++ tailWord_1039784) baseStart_1039784 baseEnd_1039784 := by
    simpa [prefixWord, tailWord_1039784, baseEnd_1039784] using wordTrace_append hprefix tailTrace_1039784
  have hstable : (prefixWord ++ tailWord_1039784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039784).length < 2 ^ (prefixWord ++ tailWord_1039784).sum := by decide
  have hdescent : baseEnd_1039784 < baseStart_1039784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039905 : List Nat := [1, 2, 3, 2, 2, 4, 2, 2, 3]
def baseStart_1039905 : Nat := 118140960795 + 1039905 * 2 ^ 59
def prefixEnd_1039905 : Nat := 4983230072969 + 3 ^ 40 * 1039905 * 2
def baseEnd_1039905 : Nat := 237320488895048489157809

theorem tailTrace_1039905 : CollatzResearch.WordTrace tailWord_1039905 prefixEnd_1039905 237320488895048489157809 := by
  unfold tailWord_1039905
  simp only [CollatzResearch.WordTrace]
  refine ⟨37928451297609261479521169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25285634198406174319680779 37928451297609261479521169)
  ·
    refine ⟨28446338473206946109640877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37928451297609261479521169 28446338473206946109640877)
    ·
      refine ⟨10667376927452604791115329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28446338473206946109640877 10667376927452604791115329)
      ·
        refine ⟨8000532695589453593336497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10667376927452604791115329 8000532695589453593336497)
        ·
          refine ⟨6000399521692090195002373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8000532695589453593336497 6000399521692090195002373)
          ·
            refine ⟨1125074910317266911562945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6000399521692090195002373 1125074910317266911562945)
            ·
              refine ⟨843806182737950183672209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1125074910317266911562945 843806182737950183672209)
              ·
                refine ⟨632854637053462637754157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 843806182737950183672209 632854637053462637754157)
                ·
                  refine ⟨237320488895048489157809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632854637053462637754157 237320488895048489157809)
                  ·
                    rfl

theorem cell21_1039905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 3].length) (baseStart_1039905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1039905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1039905 prefixEnd_1039905 := by exact prefixLift 1039905
  have htrace : WordTrace (prefixWord ++ tailWord_1039905) baseStart_1039905 baseEnd_1039905 := by
    simpa [prefixWord, tailWord_1039905, baseEnd_1039905] using wordTrace_append hprefix tailTrace_1039905
  have hstable : (prefixWord ++ tailWord_1039905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039905).length < 2 ^ (prefixWord ++ tailWord_1039905).sum := by decide
  have hdescent : baseEnd_1039905 < baseStart_1039905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039930 : List Nat := [3, 1, 1, 1, 3, 2, 3, 2, 5]
def baseStart_1039930 : Nat := 118140960795 + 1039930 * 2 ^ 59
def prefixEnd_1039930 : Nat := 4983230072969 + 3 ^ 40 * 1039930 * 2
def baseEnd_1039930 : Nat := 237326194235654001241091

theorem tailTrace_1039930 : CollatzResearch.WordTrace tailWord_1039930 prefixEnd_1039930 237326194235654001241091 := by
  unfold tailWord_1039930
  simp only [CollatzResearch.WordTrace]
  refine ⟨9482340780629672687295311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25286242081679127166120829 9482340780629672687295311)
  ·
    refine ⟨14223511170944509030942967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9482340780629672687295311 14223511170944509030942967)
    ·
      refine ⟨21335266756416763546414451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14223511170944509030942967 21335266756416763546414451)
      ·
        refine ⟨32002900134625145319621677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21335266756416763546414451 32002900134625145319621677)
        ·
          refine ⟨12001087550484429494858129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32002900134625145319621677 12001087550484429494858129)
          ·
            refine ⟨9000815662863322121143597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12001087550484429494858129 9000815662863322121143597)
            ·
              refine ⟨3375305873573745795428849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9000815662863322121143597 3375305873573745795428849)
              ·
                refine ⟨2531479405180309346571637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3375305873573745795428849 2531479405180309346571637)
                ·
                  refine ⟨237326194235654001241091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2531479405180309346571637 237326194235654001241091)
                  ·
                    rfl

theorem cell21_1039930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_1039930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1039930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1039930 prefixEnd_1039930 := by exact prefixLift 1039930
  have htrace : WordTrace (prefixWord ++ tailWord_1039930) baseStart_1039930 baseEnd_1039930 := by
    simpa [prefixWord, tailWord_1039930, baseEnd_1039930] using wordTrace_append hprefix tailTrace_1039930
  have hstable : (prefixWord ++ tailWord_1039930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039930).length < 2 ^ (prefixWord ++ tailWord_1039930).sum := by decide
  have hdescent : baseEnd_1039930 < baseStart_1039930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039933 : List Nat := [1, 4, 1, 3, 3, 1, 3, 5]
def baseStart_1039933 : Nat := 118140960795 + 1039933 * 2 ^ 59
def prefixEnd_1039933 : Nat := 4983230072969 + 3 ^ 40 * 1039933 * 2
def baseEnd_1039933 : Nat := 79108959625508887563695

theorem tailTrace_1039933 : CollatzResearch.WordTrace tailWord_1039933 prefixEnd_1039933 79108959625508887563695 := by
  unfold tailWord_1039933
  simp only [CollatzResearch.WordTrace]
  refine ⟨37929472541507822261540453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25286315027671881507693635 37929472541507822261540453)
  ·
    refine ⟨7111776101532716674038835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37929472541507822261540453 7111776101532716674038835)
    ·
      refine ⟨10667664152299075011058253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7111776101532716674038835 10667664152299075011058253)
      ·
        refine ⟨4000374057112153129146845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10667664152299075011058253 4000374057112153129146845)
        ·
          refine ⟨1500140271417057423430067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4000374057112153129146845 1500140271417057423430067)
          ·
            refine ⟨2250210407125586135145101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1500140271417057423430067 2250210407125586135145101)
            ·
              refine ⟨843828902672094800679413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2250210407125586135145101 843828902672094800679413)
              ·
                refine ⟨79108959625508887563695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 843828902672094800679413 79108959625508887563695)
                ·
                  rfl

theorem cell21_1039933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 5].length) (baseStart_1039933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1039933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1039933 prefixEnd_1039933 := by exact prefixLift 1039933
  have htrace : WordTrace (prefixWord ++ tailWord_1039933) baseStart_1039933 baseEnd_1039933 := by
    simpa [prefixWord, tailWord_1039933, baseEnd_1039933] using wordTrace_append hprefix tailTrace_1039933
  have hstable : (prefixWord ++ tailWord_1039933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039933).length < 2 ^ (prefixWord ++ tailWord_1039933).sum := by decide
  have hdescent : baseEnd_1039933 < baseStart_1039933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039964 : List Nat := [2, 2, 4, 1, 2, 1, 2, 4, 3]
def baseStart_1039964 : Nat := 118140960795 + 1039964 * 2 ^ 59
def prefixEnd_1039964 : Nat := 4983230072969 + 3 ^ 40 * 1039964 * 2
def baseEnd_1039964 : Nat := 237333953498877497674355

theorem tailTrace_1039964 : CollatzResearch.WordTrace tailWord_1039964 prefixEnd_1039964 237333953498877497674355 := by
  unfold tailWord_1039964
  simp only [CollatzResearch.WordTrace]
  refine ⟨18965301602197757277959473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25287068802930343037279297 18965301602197757277959473)
  ·
    refine ⟨14223976201648317958469605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18965301602197757277959473 14223976201648317958469605)
    ·
      refine ⟨2666995537809059617213051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14223976201648317958469605 2666995537809059617213051)
      ·
        refine ⟨4000493306713589425819577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2666995537809059617213051 4000493306713589425819577)
        ·
          refine ⟨3000369980035192069364683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4000493306713589425819577 3000369980035192069364683)
          ·
            refine ⟨4500554970052788104047025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3000369980035192069364683 4500554970052788104047025)
            ·
              refine ⟨3375416227539591078035269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4500554970052788104047025 3375416227539591078035269)
              ·
                refine ⟨632890542663673327131613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3375416227539591078035269 632890542663673327131613)
                ·
                  refine ⟨237333953498877497674355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632890542663673327131613 237333953498877497674355)
                  ·
                    rfl

theorem cell21_1039964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_1039964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1039964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1039964 prefixEnd_1039964 := by exact prefixLift 1039964
  have htrace : WordTrace (prefixWord ++ tailWord_1039964) baseStart_1039964 baseEnd_1039964 := by
    simpa [prefixWord, tailWord_1039964, baseEnd_1039964] using wordTrace_append hprefix tailTrace_1039964
  have hstable : (prefixWord ++ tailWord_1039964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039964).length < 2 ^ (prefixWord ++ tailWord_1039964).sum := by decide
  have hdescent : baseEnd_1039964 < baseStart_1039964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040023 : List Nat := [1, 1, 3, 3, 2, 4, 1, 1, 5]
def baseStart_1040023 : Nat := 118140960795 + 1040023 * 2 ^ 59
def prefixEnd_1040023 : Nat := 4983230072969 + 3 ^ 40 * 1040023 * 2
def baseEnd_1040023 : Nat := 237347418102706506190901

theorem tailTrace_1040023 : CollatzResearch.WordTrace tailWord_1040023 prefixEnd_1040023 237347418102706506190901 := by
  unfold tailWord_1040023
  simp only [CollatzResearch.WordTrace]
  refine ⟨37932755111181767632316723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25288503407454511754877815 37932755111181767632316723)
  ·
    refine ⟨56899132666772651448475085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37932755111181767632316723 56899132666772651448475085)
    ·
      refine ⟨21337174750039744293178157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56899132666772651448475085 21337174750039744293178157)
      ·
        refine ⟨8001440531264904109941809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21337174750039744293178157 8001440531264904109941809)
        ·
          refine ⟨6001080398448678082456357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8001440531264904109941809 6001080398448678082456357)
          ·
            refine ⟨1125202574709127140460567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6001080398448678082456357 1125202574709127140460567)
            ·
              refine ⟨1687803862063690710690851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125202574709127140460567 1687803862063690710690851)
              ·
                refine ⟨2531705793095536066036277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1687803862063690710690851 2531705793095536066036277)
                ·
                  refine ⟨237347418102706506190901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2531705793095536066036277 237347418102706506190901)
                  ·
                    rfl

theorem cell21_1040023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 5].length) (baseStart_1040023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1040023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1040023 prefixEnd_1040023 := by exact prefixLift 1040023
  have htrace : WordTrace (prefixWord ++ tailWord_1040023) baseStart_1040023 baseEnd_1040023 := by
    simpa [prefixWord, tailWord_1040023, baseEnd_1040023] using wordTrace_append hprefix tailTrace_1040023
  have hstable : (prefixWord ++ tailWord_1040023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040023).length < 2 ^ (prefixWord ++ tailWord_1040023).sum := by decide
  have hdescent : baseEnd_1040023 < baseStart_1040023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040074 : List Nat := [3, 1, 2, 1, 6, 1, 2, 2, 3]
def baseStart_1040074 : Nat := 118140960795 + 1040074 * 2 ^ 59
def prefixEnd_1040074 : Nat := 4983230072969 + 3 ^ 40 * 1040074 * 2
def baseEnd_1040074 : Nat := 237359056997541750840797

theorem tailTrace_1040074 : CollatzResearch.WordTrace tailWord_1040074 prefixEnd_1040074 237359056997541750840797 := by
  unfold tailWord_1040074
  simp only [CollatzResearch.WordTrace]
  refine ⟨9483653808499250835605819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25289743489331335561615517 9483653808499250835605819)
  ·
    refine ⟨14225480712748876253408729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9483653808499250835605819 14225480712748876253408729)
    ·
      refine ⟨10669110534561657190056547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14225480712748876253408729 10669110534561657190056547)
      ·
        refine ⟨16003665801842485785084821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10669110534561657190056547 16003665801842485785084821)
        ·
          refine ⟨750171834461366521175851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16003665801842485785084821 750171834461366521175851)
          ·
            refine ⟨1125257751692049781763777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750171834461366521175851 1125257751692049781763777)
            ·
              refine ⟨843943313769037336322833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1125257751692049781763777 843943313769037336322833)
              ·
                refine ⟨632957485326778002242125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 843943313769037336322833 632957485326778002242125)
                ·
                  refine ⟨237359056997541750840797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632957485326778002242125 237359056997541750840797)
                  ·
                    rfl

theorem cell21_1040074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_1040074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1040074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1040074 prefixEnd_1040074 := by exact prefixLift 1040074
  have htrace : WordTrace (prefixWord ++ tailWord_1040074) baseStart_1040074 baseEnd_1040074 := by
    simpa [prefixWord, tailWord_1040074, baseEnd_1040074] using wordTrace_append hprefix tailTrace_1040074
  have hstable : (prefixWord ++ tailWord_1040074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040074).length < 2 ^ (prefixWord ++ tailWord_1040074).sum := by decide
  have hdescent : baseEnd_1040074 < baseStart_1040074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040099 : List Nat := [1, 1, 1, 7, 2, 1, 1, 2, 5]
def baseStart_1040099 : Nat := 118140960795 + 1040099 * 2 ^ 59
def prefixEnd_1040099 : Nat := 4983230072969 + 3 ^ 40 * 1040099 * 2
def baseEnd_1040099 : Nat := 237364762338147262924079

theorem tailTrace_1040099 : CollatzResearch.WordTrace tailWord_1040099 prefixEnd_1040099 237364762338147262924079 := by
  unfold tailWord_1040099
  simp only [CollatzResearch.WordTrace]
  refine ⟨37935527058906432612083351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25290351372604288408055567 37935527058906432612083351)
  ·
    refine ⟨56903290588359648918125027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37935527058906432612083351 56903290588359648918125027)
    ·
      refine ⟨85354935882539473377187541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56903290588359648918125027 85354935882539473377187541)
      ·
        refine ⟨2000506309747018907277833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 85354935882539473377187541 2000506309747018907277833)
        ·
          refine ⟨1500379732310264180458375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2000506309747018907277833 1500379732310264180458375)
          ·
            refine ⟨2250569598465396270687563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1500379732310264180458375 2250569598465396270687563)
            ·
              refine ⟨3375854397698094406031345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2250569598465396270687563 3375854397698094406031345)
              ·
                refine ⟨2531890798273570804523509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3375854397698094406031345 2531890798273570804523509)
                ·
                  refine ⟨237364762338147262924079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2531890798273570804523509 237364762338147262924079)
                  ·
                    rfl

theorem cell21_1040099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 5].length) (baseStart_1040099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1040099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1040099 prefixEnd_1040099 := by exact prefixLift 1040099
  have htrace : WordTrace (prefixWord ++ tailWord_1040099) baseStart_1040099 baseEnd_1040099 := by
    simpa [prefixWord, tailWord_1040099, baseEnd_1040099] using wordTrace_append hprefix tailTrace_1040099
  have hstable : (prefixWord ++ tailWord_1040099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040099).length < 2 ^ (prefixWord ++ tailWord_1040099).sum := by decide
  have hdescent : baseEnd_1040099 < baseStart_1040099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040172 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 6]
def baseStart_1040172 : Nat := 118140960795 + 1040172 * 2 ^ 59
def prefixEnd_1040172 : Nat := 4983230072969 + 3 ^ 40 * 1040172 * 2
def baseEnd_1040172 : Nat := 237381421932715358207263

theorem tailTrace_1040172 : CollatzResearch.WordTrace tailWord_1040172 prefixEnd_1040172 237381421932715358207263 := by
  unfold tailWord_1040172
  simp only [CollatzResearch.WordTrace]
  refine ⟨18969094793820983039745385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25292126391761310719660513 18969094793820983039745385)
  ·
    refine ⟨14226821095365737279809039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18969094793820983039745385 14226821095365737279809039)
    ·
      refine ⟨21340231643048605919713559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14226821095365737279809039 21340231643048605919713559)
      ·
        refine ⟨32010347464572908879570339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21340231643048605919713559 32010347464572908879570339)
        ·
          refine ⟨48015521196859363319355509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32010347464572908879570339 48015521196859363319355509)
          ·
            refine ⟨4501455112205565311189579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48015521196859363319355509 4501455112205565311189579)
            ·
              refine ⟨6752182668308347966784369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4501455112205565311189579 6752182668308347966784369)
              ·
                refine ⟨5064137001231260975088277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6752182668308347966784369 5064137001231260975088277)
                ·
                  refine ⟨237381421932715358207263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5064137001231260975088277 237381421932715358207263)
                  ·
                    rfl

theorem cell21_1040172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_1040172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1040172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1040172 prefixEnd_1040172 := by exact prefixLift 1040172
  have htrace : WordTrace (prefixWord ++ tailWord_1040172) baseStart_1040172 baseEnd_1040172 := by
    simpa [prefixWord, tailWord_1040172, baseEnd_1040172] using wordTrace_append hprefix tailTrace_1040172
  have hstable : (prefixWord ++ tailWord_1040172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040172).length < 2 ^ (prefixWord ++ tailWord_1040172).sum := by decide
  have hdescent : baseEnd_1040172 < baseStart_1040172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040189 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 6]
def baseStart_1040189 : Nat := 118140960795 + 1040189 * 2 ^ 59
def prefixEnd_1040189 : Nat := 4983230072969 + 3 ^ 40 * 1040189 * 2
def baseEnd_1040189 : Nat := 237385301564327106423895

theorem tailTrace_1040189 : CollatzResearch.WordTrace tailWord_1040189 prefixEnd_1040189 237385301564327106423895 := by
  unfold tailWord_1040189
  simp only [CollatzResearch.WordTrace]
  refine ⟨37938809628580377982859621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25292539752386918655239747 37938809628580377982859621)
  ·
    refine ⟨7113526805358820871786179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37938809628580377982859621 7113526805358820871786179)
    ·
      refine ⟨10670290208038231307679269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7113526805358820871786179 10670290208038231307679269)
      ·
        refine ⟨2000679414007168370189863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10670290208038231307679269 2000679414007168370189863)
        ·
          refine ⟨3001019121010752555284795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2000679414007168370189863 3001019121010752555284795)
          ·
            refine ⟨4501528681516128832927193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3001019121010752555284795 4501528681516128832927193)
            ·
              refine ⟨3376146511137096624695395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4501528681516128832927193 3376146511137096624695395)
              ·
                refine ⟨5064219766705644937043093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376146511137096624695395 5064219766705644937043093)
                ·
                  refine ⟨237385301564327106423895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5064219766705644937043093 237385301564327106423895)
                  ·
                    rfl

theorem cell21_1040189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_1040189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1040189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1040189 prefixEnd_1040189 := by exact prefixLift 1040189
  have htrace : WordTrace (prefixWord ++ tailWord_1040189) baseStart_1040189 baseEnd_1040189 := by
    simpa [prefixWord, tailWord_1040189, baseEnd_1040189] using wordTrace_append hprefix tailTrace_1040189
  have hstable : (prefixWord ++ tailWord_1040189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040189).length < 2 ^ (prefixWord ++ tailWord_1040189).sum := by decide
  have hdescent : baseEnd_1040189 < baseStart_1040189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040217 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 7]
def baseStart_1040217 : Nat := 118140960795 + 1040217 * 2 ^ 59
def prefixEnd_1040217 : Nat := 4983230072969 + 3 ^ 40 * 1040217 * 2
def baseEnd_1040217 : Nat := 237391691545805279957171

theorem tailTrace_1040217 : CollatzResearch.WordTrace tailWord_1040217 prefixEnd_1040217 237391691545805279957171 := by
  unfold tailWord_1040217
  simp only [CollatzResearch.WordTrace]
  refine ⟨37939830872478938764878905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25293220581652625843252603 37939830872478938764878905)
  ·
    refine ⟨28454873154359204073659179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37939830872478938764878905 28454873154359204073659179)
    ·
      refine ⟨42682309731538806110488769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28454873154359204073659179 42682309731538806110488769)
      ·
        refine ⟨32011732298654104582866577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42682309731538806110488769 32011732298654104582866577)
        ·
          refine ⟨24008799223990578437149933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32011732298654104582866577 24008799223990578437149933)
          ·
            refine ⟨9003299708996466913931225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24008799223990578437149933 9003299708996466913931225)
            ·
              refine ⟨6752474781747350185448419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9003299708996466913931225 6752474781747350185448419)
              ·
                refine ⟨10128712172621025278172629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6752474781747350185448419 10128712172621025278172629)
                ·
                  refine ⟨237391691545805279957171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10128712172621025278172629 237391691545805279957171)
                  ·
                    rfl

theorem cell21_1040217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_1040217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1040217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1040217 prefixEnd_1040217 := by exact prefixLift 1040217
  have htrace : WordTrace (prefixWord ++ tailWord_1040217) baseStart_1040217 baseEnd_1040217 := by
    simpa [prefixWord, tailWord_1040217, baseEnd_1040217] using wordTrace_append hprefix tailTrace_1040217
  have hstable : (prefixWord ++ tailWord_1040217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040217).length < 2 ^ (prefixWord ++ tailWord_1040217).sum := by decide
  have hdescent : baseEnd_1040217 < baseStart_1040217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040355 : List Nat := [1, 1, 1, 6, 1, 4, 7]
def baseStart_1040355 : Nat := 118140960795 + 1040355 * 2 ^ 59
def prefixEnd_1040355 : Nat := 4983230072969 + 3 ^ 40 * 1040355 * 2
def baseEnd_1040355 : Nat := 26380353891771967406321

theorem tailTrace_1040355 : CollatzResearch.WordTrace tailWord_1040355 prefixEnd_1040355 26380353891771967406321 := by
  unfold tailWord_1040355
  simp only [CollatzResearch.WordTrace]
  refine ⟨37944864145978988333402519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25296576097319325555601679 37944864145978988333402519)
  ·
    refine ⟨56917296218968482500103779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37944864145978988333402519 56917296218968482500103779)
    ·
      refine ⟨85375944328452723750155669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56917296218968482500103779 85375944328452723750155669)
      ·
        refine ⟨4001997390396221425788547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 85375944328452723750155669 4001997390396221425788547)
        ·
          refine ⟨6002996085594332138682821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4001997390396221425788547 6002996085594332138682821)
          ·
            refine ⟨1125561766048937276003029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6002996085594332138682821 1125561766048937276003029)
            ·
              refine ⟨26380353891771967406321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1125561766048937276003029 26380353891771967406321)
              ·
                rfl

theorem cell21_1040355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 7].length) (baseStart_1040355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1040355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1040355 prefixEnd_1040355 := by exact prefixLift 1040355
  have htrace : WordTrace (prefixWord ++ tailWord_1040355) baseStart_1040355 baseEnd_1040355 := by
    simpa [prefixWord, tailWord_1040355, baseEnd_1040355] using wordTrace_append hprefix tailTrace_1040355
  have hstable : (prefixWord ++ tailWord_1040355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040355).length < 2 ^ (prefixWord ++ tailWord_1040355).sum := by decide
  have hdescent : baseEnd_1040355 < baseStart_1040355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040420 : List Nat := [2, 3, 1, 4, 2, 1, 1, 4, 3]
def baseStart_1040420 : Nat := 118140960795 + 1040420 * 2 ^ 59
def prefixEnd_1040420 : Nat := 4983230072969 + 3 ^ 40 * 1040420 * 2
def baseEnd_1040420 : Nat := 237438018911522038073423

theorem tailTrace_1040420 : CollatzResearch.WordTrace tailWord_1040420 prefixEnd_1040420 237438018911522038073423 := by
  unfold tailWord_1040420
  simp only [CollatzResearch.WordTrace]
  refine ⟨18973617445371752217259357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25298156593829002956345809 18973617445371752217259357)
  ·
    refine ⟨7115106542014407081472259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18973617445371752217259357 7115106542014407081472259)
    ·
      refine ⟨10672659813021610622208389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7115106542014407081472259 10672659813021610622208389)
      ·
        refine ⟨2001123714941551991664073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10672659813021610622208389 2001123714941551991664073)
        ·
          refine ⟨1500842786206163993748055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2001123714941551991664073 1500842786206163993748055)
          ·
            refine ⟨2251264179309245990622083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1500842786206163993748055 2251264179309245990622083)
            ·
              refine ⟨3376896268963868985933125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2251264179309245990622083 3376896268963868985933125)
              ·
                refine ⟨633168050430725434862461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3376896268963868985933125 633168050430725434862461)
                ·
                  refine ⟨237438018911522038073423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 633168050430725434862461 237438018911522038073423)
                  ·
                    rfl

theorem cell21_1040420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_1040420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1040420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1040420 prefixEnd_1040420 := by exact prefixLift 1040420
  have htrace : WordTrace (prefixWord ++ tailWord_1040420) baseStart_1040420 baseEnd_1040420 := by
    simpa [prefixWord, tailWord_1040420, baseEnd_1040420] using wordTrace_append hprefix tailTrace_1040420
  have hstable : (prefixWord ++ tailWord_1040420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040420).length < 2 ^ (prefixWord ++ tailWord_1040420).sum := by decide
  have hdescent : baseEnd_1040420 < baseStart_1040420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040459 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 8]
def baseStart_1040459 : Nat := 118140960795 + 1040459 * 2 ^ 59
def prefixEnd_1040459 : Nat := 4983230072969 + 3 ^ 40 * 1040459 * 2
def baseEnd_1040459 : Nat := 237446919242866636923343

theorem tailTrace_1040459 : CollatzResearch.WordTrace tailWord_1040459 prefixEnd_1040459 237446919242866636923343 := by
  unfold tailWord_1040459
  simp only [CollatzResearch.WordTrace]
  refine ⟨37948657337602214095188431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25299104891734809396792287 37948657337602214095188431)
  ·
    refine ⟨56922986006403321142782647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37948657337602214095188431 56922986006403321142782647)
    ·
      refine ⟨85384479009604981714173971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56922986006403321142782647 85384479009604981714173971)
      ·
        refine ⟨128076718514407472571260957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85384479009604981714173971 128076718514407472571260957)
        ·
          refine ⟨48028769442902802214222859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128076718514407472571260957 48028769442902802214222859)
          ·
            refine ⟨72043154164354203321334289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48028769442902802214222859 72043154164354203321334289)
            ·
              refine ⟨54032365623265652491000717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72043154164354203321334289 54032365623265652491000717)
              ·
                refine ⟨20262137108724619684125269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54032365623265652491000717 20262137108724619684125269)
                ·
                  refine ⟨237446919242866636923343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20262137108724619684125269 237446919242866636923343)
                  ·
                    rfl

theorem cell21_1040459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 8].length) (baseStart_1040459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1040459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1040459 prefixEnd_1040459 := by exact prefixLift 1040459
  have htrace : WordTrace (prefixWord ++ tailWord_1040459) baseStart_1040459 baseEnd_1040459 := by
    simpa [prefixWord, tailWord_1040459, baseEnd_1040459] using wordTrace_append hprefix tailTrace_1040459
  have hstable : (prefixWord ++ tailWord_1040459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040459).length < 2 ^ (prefixWord ++ tailWord_1040459).sum := by decide
  have hdescent : baseEnd_1040459 < baseStart_1040459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040513 : List Nat := [1, 2, 4, 2, 4, 1, 1, 3, 3]
def baseStart_1040513 : Nat := 118140960795 + 1040513 * 2 ^ 59
def prefixEnd_1040513 : Nat := 4983230072969 + 3 ^ 40 * 1040513 * 2
def baseEnd_1040513 : Nat := 237459242778574543023233

theorem tailTrace_1040513 : CollatzResearch.WordTrace tailWord_1040513 prefixEnd_1040513 237459242778574543023233 := by
  unfold tailWord_1040513
  simp only [CollatzResearch.WordTrace]
  refine ⟨37950626879406581317654193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25300417919604387545102795 37950626879406581317654193)
  ·
    refine ⟨28462970159554935988240645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37950626879406581317654193 28462970159554935988240645)
    ·
      refine ⟨5336806904916550497795121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28462970159554935988240645 5336806904916550497795121)
      ·
        refine ⟨4002605178687412873346341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5336806904916550497795121 4002605178687412873346341)
        ·
          refine ⟨750488471003889913752439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4002605178687412873346341 750488471003889913752439)
          ·
            refine ⟨1125732706505834870628659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750488471003889913752439 1125732706505834870628659)
            ·
              refine ⟨1688599059758752305942989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125732706505834870628659 1688599059758752305942989)
              ·
                refine ⟨633224647409532114728621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1688599059758752305942989 633224647409532114728621)
                ·
                  refine ⟨237459242778574543023233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 633224647409532114728621 237459242778574543023233)
                  ·
                    rfl

theorem cell21_1040513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 3].length) (baseStart_1040513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1040513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1040513 prefixEnd_1040513 := by exact prefixLift 1040513
  have htrace : WordTrace (prefixWord ++ tailWord_1040513) baseStart_1040513 baseEnd_1040513 := by
    simpa [prefixWord, tailWord_1040513, baseEnd_1040513] using wordTrace_append hprefix tailTrace_1040513
  have hstable : (prefixWord ++ tailWord_1040513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040513).length < 2 ^ (prefixWord ++ tailWord_1040513).sum := by decide
  have hdescent : baseEnd_1040513 < baseStart_1040513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040673 : List Nat := [1, 2, 3, 2, 1, 1, 4, 2, 5]
def baseStart_1040673 : Nat := 118140960795 + 1040673 * 2 ^ 59
def prefixEnd_1040673 : Nat := 4983230072969 + 3 ^ 40 * 1040673 * 2
def baseEnd_1040673 : Nat := 237495756958449820356239

theorem tailTrace_1040673 : CollatzResearch.WordTrace tailWord_1040673 prefixEnd_1040673 237495756958449820356239 := by
  unfold tailWord_1040673
  simp only [CollatzResearch.WordTrace]
  refine ⟨37956462558826928643478673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25304308372551285762319115 37956462558826928643478673)
  ·
    refine ⟨28467346919120196482609005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37956462558826928643478673 28467346919120196482609005)
    ·
      refine ⟨10675255094670073680978377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28467346919120196482609005 10675255094670073680978377)
      ·
        refine ⟨8006441321002555260733783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10675255094670073680978377 8006441321002555260733783)
        ·
          refine ⟨12009661981503832891100675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8006441321002555260733783 12009661981503832891100675)
          ·
            refine ⟨18014492972255749336651013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12009661981503832891100675 18014492972255749336651013)
            ·
              refine ⟨3377717432297953000622065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18014492972255749336651013 3377717432297953000622065)
              ·
                refine ⟨2533288074223464750466549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3377717432297953000622065 2533288074223464750466549)
                ·
                  refine ⟨237495756958449820356239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2533288074223464750466549 237495756958449820356239)
                  ·
                    rfl

theorem cell21_1040673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_1040673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1040673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1040673 prefixEnd_1040673 := by exact prefixLift 1040673
  have htrace : WordTrace (prefixWord ++ tailWord_1040673) baseStart_1040673 baseEnd_1040673 := by
    simpa [prefixWord, tailWord_1040673, baseEnd_1040673] using wordTrace_append hprefix tailTrace_1040673
  have hstable : (prefixWord ++ tailWord_1040673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040673).length < 2 ^ (prefixWord ++ tailWord_1040673).sum := by decide
  have hdescent : baseEnd_1040673 < baseStart_1040673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040676 : List Nat := [2, 3, 1, 3, 1, 4, 2, 5]
def baseStart_1040676 : Nat := 118140960795 + 1040676 * 2 ^ 59
def prefixEnd_1040676 : Nat := 4983230072969 + 3 ^ 40 * 1040676 * 2
def baseEnd_1040676 : Nat := 79165480533107493935411

theorem tailTrace_1040676 : CollatzResearch.WordTrace tailWord_1040676 prefixEnd_1040676 79165480533107493935411 := by
  unfold tailWord_1040676
  simp only [CollatzResearch.WordTrace]
  refine ⟨18978285988908030077918941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25304381318544040103891921 18978285988908030077918941)
  ·
    refine ⟨7116857245840511279219603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18978285988908030077918941 7116857245840511279219603)
    ·
      refine ⟨10675285868760766918829405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7116857245840511279219603 10675285868760766918829405)
      ·
        refine ⟨4003232200785287594561027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10675285868760766918829405 4003232200785287594561027)
        ·
          refine ⟨6004848301177931391841541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4003232200785287594561027 6004848301177931391841541)
          ·
            refine ⟨1125909056470862135970289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6004848301177931391841541 1125909056470862135970289)
            ·
              refine ⟨844431792353146601977717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1125909056470862135970289 844431792353146601977717)
              ·
                refine ⟨79165480533107493935411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 844431792353146601977717 79165480533107493935411)
                ·
                  rfl

theorem cell21_1040676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 5].length) (baseStart_1040676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1040676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1040676 prefixEnd_1040676 := by exact prefixLift 1040676
  have htrace : WordTrace (prefixWord ++ tailWord_1040676) baseStart_1040676 baseEnd_1040676 := by
    simpa [prefixWord, tailWord_1040676, baseEnd_1040676] using wordTrace_append hprefix tailTrace_1040676
  have hstable : (prefixWord ++ tailWord_1040676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040676).length < 2 ^ (prefixWord ++ tailWord_1040676).sum := by decide
  have hdescent : baseEnd_1040676 < baseStart_1040676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040687 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 6]
def baseStart_1040687 : Nat := 118140960795 + 1040687 * 2 ^ 59
def prefixEnd_1040687 : Nat := 4983230072969 + 3 ^ 40 * 1040687 * 2
def baseEnd_1040687 : Nat := 237498951949188907122877

theorem tailTrace_1040687 : CollatzResearch.WordTrace tailWord_1040687 prefixEnd_1040687 237498951949188907122877 := by
  unfold tailWord_1040687
  simp only [CollatzResearch.WordTrace]
  refine ⟨37956973180776209034488315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25304648787184139356325543 37956973180776209034488315)
  ·
    refine ⟨56935459771164313551732473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37956973180776209034488315 56935459771164313551732473)
    ·
      refine ⟨42701594828373235163799355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56935459771164313551732473 42701594828373235163799355)
      ·
        refine ⟨64052392242559852745699033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42701594828373235163799355 64052392242559852745699033)
        ·
          refine ⟨48039294181919889559274275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64052392242559852745699033 48039294181919889559274275)
          ·
            refine ⟨72058941272879834338911413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48039294181919889559274275 72058941272879834338911413)
            ·
              refine ⟨6755525744332484469272945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72058941272879834338911413 6755525744332484469272945)
              ·
                refine ⟨5066644308249363351954709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6755525744332484469272945 5066644308249363351954709)
                ·
                  refine ⟨237498951949188907122877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5066644308249363351954709 237498951949188907122877)
                  ·
                    rfl

theorem cell21_1040687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 6].length) (baseStart_1040687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1040687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1040687 prefixEnd_1040687 := by exact prefixLift 1040687
  have htrace : WordTrace (prefixWord ++ tailWord_1040687) baseStart_1040687 baseEnd_1040687 := by
    simpa [prefixWord, tailWord_1040687, baseEnd_1040687] using wordTrace_append hprefix tailTrace_1040687
  have hstable : (prefixWord ++ tailWord_1040687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040687).length < 2 ^ (prefixWord ++ tailWord_1040687).sum := by decide
  have hdescent : baseEnd_1040687 < baseStart_1040687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040721 : List Nat := [1, 2, 2, 1, 4, 2, 4, 1, 4]
def baseStart_1040721 : Nat := 118140960795 + 1040721 * 2 ^ 59
def prefixEnd_1040721 : Nat := 4983230072969 + 3 ^ 40 * 1040721 * 2
def baseEnd_1040721 : Nat := 237506711212412403556141

theorem tailTrace_1040721 : CollatzResearch.WordTrace tailWord_1040721 prefixEnd_1040721 237506711212412403556141 := by
  unfold tailWord_1040721
  simp only [CollatzResearch.WordTrace]
  refine ⟨37958213262653032841226017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25305475508435355227484011 37958213262653032841226017)
  ·
    refine ⟨28468659946989774630919513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37958213262653032841226017 28468659946989774630919513)
    ·
      refine ⟨21351494960242330973189635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28468659946989774630919513 21351494960242330973189635)
      ·
        refine ⟨32027242440363496459784453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21351494960242330973189635 32027242440363496459784453)
        ·
          refine ⟨6005107957568155586209585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32027242440363496459784453 6005107957568155586209585)
          ·
            refine ⟨4503830968176116689657189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6005107957568155586209585 4503830968176116689657189)
            ·
              refine ⟨844468306533021879310723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4503830968176116689657189 844468306533021879310723)
              ·
                refine ⟨1266702459799532818966085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 844468306533021879310723 1266702459799532818966085)
                ·
                  refine ⟨237506711212412403556141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1266702459799532818966085 237506711212412403556141)
                  ·
                    rfl

theorem cell21_1040721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 4].length) (baseStart_1040721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1040721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1040721 prefixEnd_1040721 := by exact prefixLift 1040721
  have htrace : WordTrace (prefixWord ++ tailWord_1040721) baseStart_1040721 baseEnd_1040721 := by
    simpa [prefixWord, tailWord_1040721, baseEnd_1040721] using wordTrace_append hprefix tailTrace_1040721
  have hstable : (prefixWord ++ tailWord_1040721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040721).length < 2 ^ (prefixWord ++ tailWord_1040721).sum := by decide
  have hdescent : baseEnd_1040721 < baseStart_1040721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040758 : List Nat := [5, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_1040758 : Nat := 118140960795 + 1040758 * 2 ^ 59
def prefixEnd_1040758 : Nat := 4983230072969 + 3 ^ 40 * 1040758 * 2
def baseEnd_1040758 : Nat := 237515155116508561439399

theorem tailTrace_1040758 : CollatzResearch.WordTrace tailWord_1040758 prefixEnd_1040758 237515155116508561439399 := by
  unfold tailWord_1040758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2372472672719936760020183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25306375175679325440215285 2372472672719936760020183)
  ·
    refine ⟨3558709009079905140030275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2372472672719936760020183 3558709009079905140030275)
    ·
      refine ⟨5338063513619857710045413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3558709009079905140030275 5338063513619857710045413)
      ·
        refine ⟨1000886908803723320633515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5338063513619857710045413 1000886908803723320633515)
        ·
          refine ⟨1501330363205584980950273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1000886908803723320633515 1501330363205584980950273)
          ·
            refine ⟨1125997772404188735712705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1501330363205584980950273 1125997772404188735712705)
            ·
              refine ⟨844498329303141551784529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1125997772404188735712705 844498329303141551784529)
              ·
                refine ⟨633373746977356163838397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 844498329303141551784529 633373746977356163838397)
                ·
                  refine ⟨237515155116508561439399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 633373746977356163838397 237515155116508561439399)
                  ·
                    rfl

theorem cell21_1040758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_1040758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1040758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1040758 prefixEnd_1040758 := by exact prefixLift 1040758
  have htrace : WordTrace (prefixWord ++ tailWord_1040758) baseStart_1040758 baseEnd_1040758 := by
    simpa [prefixWord, tailWord_1040758, baseEnd_1040758] using wordTrace_append hprefix tailTrace_1040758
  have hstable : (prefixWord ++ tailWord_1040758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040758).length < 2 ^ (prefixWord ++ tailWord_1040758).sum := by decide
  have hdescent : baseEnd_1040758 < baseStart_1040758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040780 : List Nat := [2, 2, 1, 2, 1, 4, 2, 3, 4]
def baseStart_1040780 : Nat := 118140960795 + 1040780 * 2 ^ 59
def prefixEnd_1040780 : Nat := 4983230072969 + 3 ^ 40 * 1040780 * 2
def baseEnd_1040780 : Nat := 237520175816241412072687

theorem tailTrace_1040780 : CollatzResearch.WordTrace tailWord_1040780 prefixEnd_1040780 237520175816241412072687 := by
  unfold tailWord_1040780
  simp only [CollatzResearch.WordTrace]
  refine ⟨18980182584719642958811897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25306910112959523945082529 18980182584719642958811897)
  ·
    refine ⟨14235136938539732219108923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18980182584719642958811897 14235136938539732219108923)
    ·
      refine ⟨21352705407809598328663385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14235136938539732219108923 21352705407809598328663385)
      ·
        refine ⟨16014529055857198746497539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21352705407809598328663385 16014529055857198746497539)
        ·
          refine ⟨24021793583785798119746309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16014529055857198746497539 24021793583785798119746309)
          ·
            refine ⟨4504086296959837147452433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24021793583785798119746309 4504086296959837147452433)
            ·
              refine ⟨3378064722719877860589325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4504086296959837147452433 3378064722719877860589325)
              ·
                refine ⟨1266774271019954197720997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3378064722719877860589325 1266774271019954197720997)
                ·
                  refine ⟨237520175816241412072687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1266774271019954197720997 237520175816241412072687)
                  ·
                    rfl

theorem cell21_1040780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_1040780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1040780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1040780 prefixEnd_1040780 := by exact prefixLift 1040780
  have htrace : WordTrace (prefixWord ++ tailWord_1040780) baseStart_1040780 baseEnd_1040780 := by
    simpa [prefixWord, tailWord_1040780, baseEnd_1040780] using wordTrace_append hprefix tailTrace_1040780
  have hstable : (prefixWord ++ tailWord_1040780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040780).length < 2 ^ (prefixWord ++ tailWord_1040780).sum := by decide
  have hdescent : baseEnd_1040780 < baseStart_1040780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040825 : List Nat := [1, 2, 1, 4, 3, 1, 1, 3, 5]
def baseStart_1040825 : Nat := 118140960795 + 1040825 * 2 ^ 59
def prefixEnd_1040825 : Nat := 4983230072969 + 3 ^ 40 * 1040825 * 2
def baseEnd_1040825 : Nat := 237530445429331333822595

theorem tailTrace_1040825 : CollatzResearch.WordTrace tailWord_1040825 prefixEnd_1040825 237530445429331333822595 := by
  unfold tailWord_1040825
  simp only [CollatzResearch.WordTrace]
  refine ⟨37962006454276258603011929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25308004302850839068674619 37962006454276258603011929)
  ·
    refine ⟨28471504840707193952258947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37962006454276258603011929 28471504840707193952258947)
    ·
      refine ⟨42707257261060790928388421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28471504840707193952258947 42707257261060790928388421)
      ·
        refine ⟨8007610736448898299072829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42707257261060790928388421 8007610736448898299072829)
        ·
          refine ⟨3002854026168336862152311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8007610736448898299072829 3002854026168336862152311)
          ·
            refine ⟨4504281039252505293228467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3002854026168336862152311 4504281039252505293228467)
            ·
              refine ⟨6756421558878757939842701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4504281039252505293228467 6756421558878757939842701)
              ·
                refine ⟨2533658084579534227441013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6756421558878757939842701 2533658084579534227441013)
                ·
                  refine ⟨237530445429331333822595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2533658084579534227441013 237530445429331333822595)
                  ·
                    rfl

theorem cell21_1040825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_1040825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1040825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1040825 prefixEnd_1040825 := by exact prefixLift 1040825
  have htrace : WordTrace (prefixWord ++ tailWord_1040825) baseStart_1040825 baseEnd_1040825 := by
    simpa [prefixWord, tailWord_1040825, baseEnd_1040825] using wordTrace_append hprefix tailTrace_1040825
  have hstable : (prefixWord ++ tailWord_1040825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040825).length < 2 ^ (prefixWord ++ tailWord_1040825).sum := by decide
  have hdescent : baseEnd_1040825 < baseStart_1040825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040946 : List Nat := [3, 2, 1, 1, 2, 1, 5, 6]
def baseStart_1040946 : Nat := 118140960795 + 1040946 * 2 ^ 59
def prefixEnd_1040946 : Nat := 4983230072969 + 3 ^ 40 * 1040946 * 2
def baseEnd_1040946 : Nat := 79186019759287337435227

theorem tailTrace_1040946 : CollatzResearch.WordTrace tailWord_1040946 prefixEnd_1040946 79186019759287337435227 := by
  unfold tailWord_1040946
  simp only [CollatzResearch.WordTrace]
  refine ⟨9491604921709474067041673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25310946457891930845444461 9491604921709474067041673)
  ·
    refine ⟨7118703691282105550281255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9491604921709474067041673 7118703691282105550281255)
    ·
      refine ⟨10678055536923158325421883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7118703691282105550281255 10678055536923158325421883)
      ·
        refine ⟨16017083305384737488132825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10678055536923158325421883 16017083305384737488132825)
        ·
          refine ⟨12012812479038553116099619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16017083305384737488132825 12012812479038553116099619)
          ·
            refine ⟨18019218718557829674149429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12012812479038553116099619 18019218718557829674149429)
            ·
              refine ⟨1689301754864796531951509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18019218718557829674149429 1689301754864796531951509)
              ·
                refine ⟨79186019759287337435227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1689301754864796531951509 79186019759287337435227)
                ·
                  rfl

theorem cell21_1040946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_1040946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1040946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1040946 prefixEnd_1040946 := by exact prefixLift 1040946
  have htrace : WordTrace (prefixWord ++ tailWord_1040946) baseStart_1040946 baseEnd_1040946 := by
    simpa [prefixWord, tailWord_1040946, baseEnd_1040946] using wordTrace_append hprefix tailTrace_1040946
  have hstable : (prefixWord ++ tailWord_1040946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040946).length < 2 ^ (prefixWord ++ tailWord_1040946).sum := by decide
  have hdescent : baseEnd_1040946 < baseStart_1040946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040960 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 7]
def baseStart_1040960 : Nat := 118140960795 + 1040960 * 2 ^ 59
def prefixEnd_1040960 : Nat := 4983230072969 + 3 ^ 40 * 1040960 * 2
def baseEnd_1040960 : Nat := 237561254268601099072319

theorem tailTrace_1040960 : CollatzResearch.WordTrace tailWord_1040960 prefixEnd_1040960 237561254268601099072319 := by
  unfold tailWord_1040960
  simp only [CollatzResearch.WordTrace]
  refine ⟨18983465154393588329588167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25311286872524784439450889 18983465154393588329588167)
  ·
    refine ⟨28475197731590382494382251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18983465154393588329588167 28475197731590382494382251)
    ·
      refine ⟨42712796597385573741573377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28475197731590382494382251 42712796597385573741573377)
      ·
        refine ⟨32034597448039180306180033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42712796597385573741573377 32034597448039180306180033)
        ·
          refine ⟨24025948086029385229635025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32034597448039180306180033 24025948086029385229635025)
          ·
            refine ⟨18019461064522038922226269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24025948086029385229635025 18019461064522038922226269)
            ·
              refine ⟨6757297899195764595834851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18019461064522038922226269 6757297899195764595834851)
              ·
                refine ⟨10135946848793646893752277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6757297899195764595834851 10135946848793646893752277)
                ·
                  refine ⟨237561254268601099072319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10135946848793646893752277 237561254268601099072319)
                  ·
                    rfl

theorem cell21_1040960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_1040960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1040960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1040960 prefixEnd_1040960 := by exact prefixLift 1040960
  have htrace : WordTrace (prefixWord ++ tailWord_1040960) baseStart_1040960 baseEnd_1040960 := by
    simpa [prefixWord, tailWord_1040960, baseEnd_1040960] using wordTrace_append hprefix tailTrace_1040960
  have hstable : (prefixWord ++ tailWord_1040960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040960).length < 2 ^ (prefixWord ++ tailWord_1040960).sum := by decide
  have hdescent : baseEnd_1040960 < baseStart_1040960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041053 : List Nat := [1, 4, 2, 1, 1, 1, 5, 1, 5]
def baseStart_1041053 : Nat := 118140960795 + 1041053 * 2 ^ 59
def prefixEnd_1041053 : Nat := 4983230072969 + 3 ^ 40 * 1041053 * 2
def baseEnd_1041053 : Nat := 237582478135653604022129

theorem tailTrace_1041053 : CollatzResearch.WordTrace tailWord_1041053 prefixEnd_1041053 237582478135653604022129 := by
  unfold tailWord_1041053
  simp only [CollatzResearch.WordTrace]
  refine ⟨37970322297450253542311813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25313548198300169028207875 37970322297450253542311813)
  ·
    refine ⟨7119435430771922539183465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37970322297450253542311813 7119435430771922539183465)
    ·
      refine ⟨5339576573078941904387599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7119435430771922539183465 5339576573078941904387599)
      ·
        refine ⟨8009364859618412856581399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5339576573078941904387599 8009364859618412856581399)
        ·
          refine ⟨12014047289427619284872099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8009364859618412856581399 12014047289427619284872099)
          ·
            refine ⟨18021070934141428927308149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12014047289427619284872099 18021070934141428927308149)
            ·
              refine ⟨1689475400075758961935139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18021070934141428927308149 1689475400075758961935139)
              ·
                refine ⟨2534213100113638442902709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1689475400075758961935139 2534213100113638442902709)
                ·
                  refine ⟨237582478135653604022129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2534213100113638442902709 237582478135653604022129)
                  ·
                    rfl

theorem cell21_1041053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_1041053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1041053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1041053 prefixEnd_1041053 := by exact prefixLift 1041053
  have htrace : WordTrace (prefixWord ++ tailWord_1041053) baseStart_1041053 baseEnd_1041053 := by
    simpa [prefixWord, tailWord_1041053, baseEnd_1041053] using wordTrace_append hprefix tailTrace_1041053
  have hstable : (prefixWord ++ tailWord_1041053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041053).length < 2 ^ (prefixWord ++ tailWord_1041053).sum := by decide
  have hdescent : baseEnd_1041053 < baseStart_1041053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041160 : List Nat := [2, 1, 3, 2, 2, 2, 3, 2, 4]
def baseStart_1041160 : Nat := 118140960795 + 1041160 * 2 ^ 59
def prefixEnd_1041160 : Nat := 4983230072969 + 3 ^ 40 * 1041160 * 2
def baseEnd_1041160 : Nat := 237606896993445195738577

theorem tailTrace_1041160 : CollatzResearch.WordTrace tailWord_1041160 prefixEnd_1041160 237606896993445195738577 := by
  unfold tailWord_1041160
  simp only [CollatzResearch.WordTrace]
  refine ⟨18987112454031305408228467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25316149938708407210971289 18987112454031305408228467)
  ·
    refine ⟨28480668681046958112342701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18987112454031305408228467 28480668681046958112342701)
    ·
      refine ⟨10680250755392609292128513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28480668681046958112342701 10680250755392609292128513)
      ·
        refine ⟨8010188066544456969096385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10680250755392609292128513 8010188066544456969096385)
        ·
          refine ⟨6007641049908342726822289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8010188066544456969096385 6007641049908342726822289)
          ·
            refine ⟨4505730787431257045116717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6007641049908342726822289 4505730787431257045116717)
            ·
              refine ⟨1689649045286721391918769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4505730787431257045116717 1689649045286721391918769)
              ·
                refine ⟨1267236783965041043939077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1689649045286721391918769 1267236783965041043939077)
                ·
                  refine ⟨237606896993445195738577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1267236783965041043939077 237606896993445195738577)
                  ·
                    rfl

theorem cell21_1041160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 4].length) (baseStart_1041160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1041160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1041160 prefixEnd_1041160 := by exact prefixLift 1041160
  have htrace : WordTrace (prefixWord ++ tailWord_1041160) baseStart_1041160 baseEnd_1041160 := by
    simpa [prefixWord, tailWord_1041160, baseEnd_1041160] using wordTrace_append hprefix tailTrace_1041160
  have hstable : (prefixWord ++ tailWord_1041160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041160).length < 2 ^ (prefixWord ++ tailWord_1041160).sum := by decide
  have hdescent : baseEnd_1041160 < baseStart_1041160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041197 : List Nat := [1, 5, 3, 2, 1, 2, 1, 3, 3]
def baseStart_1041197 : Nat := 118140960795 + 1041197 * 2 ^ 59
def prefixEnd_1041197 : Nat := 4983230072969 + 3 ^ 40 * 1041197 * 2
def baseEnd_1041197 : Nat := 237615340897541353621835

theorem tailTrace_1041197 : CollatzResearch.WordTrace tailWord_1041197 prefixEnd_1041197 237615340897541353621835 := by
  unfold tailWord_1041197
  simp only [CollatzResearch.WordTrace]
  refine ⟨37975574408928566135553845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25317049605952377423702563 37975574408928566135553845)
  ·
    refine ⟨3560210100837053075208173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37975574408928566135553845 3560210100837053075208173)
    ·
      refine ⟨1335078787813894903203065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3560210100837053075208173 1335078787813894903203065)
      ·
        refine ⟨1001309090860421177402299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1335078787813894903203065 1001309090860421177402299)
        ·
          refine ⟨1501963636290631766103449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001309090860421177402299 1501963636290631766103449)
          ·
            refine ⟨1126472727217973824577587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1501963636290631766103449 1126472727217973824577587)
            ·
              refine ⟨1689709090826960736866381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1126472727217973824577587 1689709090826960736866381)
              ·
                refine ⟨633640909060110276324893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1689709090826960736866381 633640909060110276324893)
                ·
                  refine ⟨237615340897541353621835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 633640909060110276324893 237615340897541353621835)
                  ·
                    rfl

theorem cell21_1041197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_1041197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1041197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1041197 prefixEnd_1041197 := by exact prefixLift 1041197
  have htrace : WordTrace (prefixWord ++ tailWord_1041197) baseStart_1041197 baseEnd_1041197 := by
    simpa [prefixWord, tailWord_1041197, baseEnd_1041197] using wordTrace_append hprefix tailTrace_1041197
  have hstable : (prefixWord ++ tailWord_1041197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041197).length < 2 ^ (prefixWord ++ tailWord_1041197).sum := by decide
  have hdescent : baseEnd_1041197 < baseStart_1041197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041219 : List Nat := [1, 1, 1, 3, 1, 4, 2, 4, 4]
def baseStart_1041219 : Nat := 118140960795 + 1041219 * 2 ^ 59
def prefixEnd_1041219 : Nat := 4983230072969 + 3 ^ 40 * 1041219 * 2
def baseEnd_1041219 : Nat := 237620361597274204255123

theorem tailTrace_1041219 : CollatzResearch.WordTrace tailWord_1041219 prefixEnd_1041219 237620361597274204255123 := by
  unfold tailWord_1041219
  simp only [CollatzResearch.WordTrace]
  refine ⟨37976376814848863892854711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25317584543232575928569807 37976376814848863892854711)
  ·
    refine ⟨56964565222273295839282067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37976376814848863892854711 56964565222273295839282067)
    ·
      refine ⟨85446847833409943758923101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56964565222273295839282067 85446847833409943758923101)
      ·
        refine ⟨32042567937528728909596163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85446847833409943758923101 32042567937528728909596163)
        ·
          refine ⟨48063851906293093364394245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32042567937528728909596163 48063851906293093364394245)
          ·
            refine ⟨9011972232429955005823921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48063851906293093364394245 9011972232429955005823921)
            ·
              refine ⟨6758979174322466254367941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9011972232429955005823921 6758979174322466254367941)
              ·
                refine ⟨1267308595185462422693989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6758979174322466254367941 1267308595185462422693989)
                ·
                  refine ⟨237620361597274204255123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1267308595185462422693989 237620361597274204255123)
                  ·
                    rfl

theorem cell21_1041219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 4].length) (baseStart_1041219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1041219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1041219 prefixEnd_1041219 := by exact prefixLift 1041219
  have htrace : WordTrace (prefixWord ++ tailWord_1041219) baseStart_1041219 baseEnd_1041219 := by
    simpa [prefixWord, tailWord_1041219, baseEnd_1041219] using wordTrace_append hprefix tailTrace_1041219
  have hstable : (prefixWord ++ tailWord_1041219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041219).length < 2 ^ (prefixWord ++ tailWord_1041219).sum := by decide
  have hdescent : baseEnd_1041219 < baseStart_1041219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041298 : List Nat := [3, 2, 3, 2, 2, 1, 1, 2, 5]
def baseStart_1041298 : Nat := 118140960795 + 1041298 * 2 ^ 59
def prefixEnd_1041298 : Nat := 4983230072969 + 3 ^ 40 * 1041298 * 2
def baseEnd_1041298 : Nat := 237638390473587622438295

theorem tailTrace_1041298 : CollatzResearch.WordTrace tailWord_1041298 prefixEnd_1041298 237638390473587622438295 := by
  unfold tailWord_1041298
  simp only [CollatzResearch.WordTrace]
  refine ⟨9494814545390665096245137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25319505454375106923320365 9494814545390665096245137)
  ·
    refine ⟨7121110909042998822183853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9494814545390665096245137 7121110909042998822183853)
    ·
      refine ⟨2670416590891124558318945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7121110909042998822183853 2670416590891124558318945)
      ·
        refine ⟨2002812443168343418739209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2670416590891124558318945 2002812443168343418739209)
        ·
          refine ⟨1502109332376257564054407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2002812443168343418739209 1502109332376257564054407)
          ·
            refine ⟨2253163998564386346081611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502109332376257564054407 2253163998564386346081611)
            ·
              refine ⟨3379745997846579519122417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2253163998564386346081611 3379745997846579519122417)
              ·
                refine ⟨2534809498384934639341813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3379745997846579519122417 2534809498384934639341813)
                ·
                  refine ⟨237638390473587622438295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2534809498384934639341813 237638390473587622438295)
                  ·
                    rfl

theorem cell21_1041298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_1041298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1041298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1041298 prefixEnd_1041298 := by exact prefixLift 1041298
  have htrace : WordTrace (prefixWord ++ tailWord_1041298) baseStart_1041298 baseEnd_1041298 := by
    simpa [prefixWord, tailWord_1041298, baseEnd_1041298] using wordTrace_append hprefix tailTrace_1041298
  have hstable : (prefixWord ++ tailWord_1041298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041298).length < 2 ^ (prefixWord ++ tailWord_1041298).sum := by decide
  have hdescent : baseEnd_1041298 < baseStart_1041298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041329 : List Nat := [1, 2, 2, 4, 3, 2, 1, 2, 4]
def baseStart_1041329 : Nat := 118140960795 + 1041329 * 2 ^ 59
def prefixEnd_1041329 : Nat := 4983230072969 + 3 ^ 40 * 1041329 * 2
def baseEnd_1041329 : Nat := 237645465095938457421565

theorem tailTrace_1041329 : CollatzResearch.WordTrace tailWord_1041329 prefixEnd_1041329 237645465095938457421565 := by
  unfold tailWord_1041329
  simp only [CollatzResearch.WordTrace]
  refine ⟨37980388844450352679359041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25320259229633568452906027 37980388844450352679359041)
  ·
    refine ⟨28485291633337764509519281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37980388844450352679359041 28485291633337764509519281)
    ·
      refine ⟨21363968725003323382139461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28485291633337764509519281 21363968725003323382139461)
      ·
        refine ⟨4005744135938123134151149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21363968725003323382139461 4005744135938123134151149)
        ·
          refine ⟨1502154050976796175306681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4005744135938123134151149 1502154050976796175306681)
          ·
            refine ⟨1126615538232597131480011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1502154050976796175306681 1126615538232597131480011)
            ·
              refine ⟨1689923307348895697220017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1126615538232597131480011 1689923307348895697220017)
              ·
                refine ⟨1267442480511671772915013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1689923307348895697220017 1267442480511671772915013)
                ·
                  refine ⟨237645465095938457421565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1267442480511671772915013 237645465095938457421565)
                  ·
                    rfl

theorem cell21_1041329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 4].length) (baseStart_1041329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1041329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1041329 prefixEnd_1041329 := by exact prefixLift 1041329
  have htrace : WordTrace (prefixWord ++ tailWord_1041329) baseStart_1041329 baseEnd_1041329 := by
    simpa [prefixWord, tailWord_1041329, baseEnd_1041329] using wordTrace_append hprefix tailTrace_1041329
  have hstable : (prefixWord ++ tailWord_1041329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041329).length < 2 ^ (prefixWord ++ tailWord_1041329).sum := by decide
  have hdescent : baseEnd_1041329 < baseStart_1041329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041509 : List Nat := [1, 3, 1, 3, 2, 1, 1, 6, 3]
def baseStart_1041509 : Nat := 118140960795 + 1041509 * 2 ^ 59
def prefixEnd_1041509 : Nat := 4983230072969 + 3 ^ 40 * 1041509 * 2
def baseEnd_1041509 : Nat := 237686543548298144421197

theorem tailTrace_1041509 : CollatzResearch.WordTrace tailWord_1041509 prefixEnd_1041509 237686543548298144421197 := by
  unfold tailWord_1041509
  simp only [CollatzResearch.WordTrace]
  refine ⟨37986953983798243420911581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25324635989198828947274387 37986953983798243420911581)
  ·
    refine ⟨14245107743924341282841843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37986953983798243420911581 14245107743924341282841843)
    ·
      refine ⟨21367661615886511924262765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14245107743924341282841843 21367661615886511924262765)
      ·
        refine ⟨8012873105957441971598537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21367661615886511924262765 8012873105957441971598537)
        ·
          refine ⟨6009654829468081478698903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8012873105957441971598537 6009654829468081478698903)
          ·
            refine ⟨9014482244202122218048355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6009654829468081478698903 9014482244202122218048355)
            ·
              refine ⟨13521723366303183327072533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9014482244202122218048355 13521723366303183327072533)
              ·
                refine ⟨633830782795461718456525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13521723366303183327072533 633830782795461718456525)
                ·
                  refine ⟨237686543548298144421197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 633830782795461718456525 237686543548298144421197)
                  ·
                    rfl

theorem cell21_1041509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_1041509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1041509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1041509 prefixEnd_1041509 := by exact prefixLift 1041509
  have htrace : WordTrace (prefixWord ++ tailWord_1041509) baseStart_1041509 baseEnd_1041509 := by
    simpa [prefixWord, tailWord_1041509, baseEnd_1041509] using wordTrace_append hprefix tailTrace_1041509
  have hstable : (prefixWord ++ tailWord_1041509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041509).length < 2 ^ (prefixWord ++ tailWord_1041509).sum := by decide
  have hdescent : baseEnd_1041509 < baseStart_1041509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041554 : List Nat := [3, 2, 3, 1, 1, 4, 7]
def baseStart_1041554 : Nat := 118140960795 + 1041554 * 2 ^ 59
def prefixEnd_1041554 : Nat := 4983230072969 + 3 ^ 40 * 1041554 * 2
def baseEnd_1041554 : Nat := 26410757017932007352345

theorem tailTrace_1041554 : CollatzResearch.WordTrace tailWord_1041554 prefixEnd_1041554 26410757017932007352345 := by
  unfold tailWord_1041554
  simp only [CollatzResearch.WordTrace]
  refine ⟨9497148817158804026574929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25325730179090144070866477 9497148817158804026574929)
  ·
    refine ⟨7122861612869103019931197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9497148817158804026574929 7122861612869103019931197)
    ·
      refine ⟨2671073104825913632474199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7122861612869103019931197 2671073104825913632474199)
      ·
        refine ⟨4006609657238870448711299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2671073104825913632474199 4006609657238870448711299)
        ·
          refine ⟨6009914485858305673066949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4006609657238870448711299 6009914485858305673066949)
          ·
            refine ⟨1126858966098432313700053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6009914485858305673066949 1126858966098432313700053)
            ·
              refine ⟨26410757017932007352345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1126858966098432313700053 26410757017932007352345)
              ·
                rfl

theorem cell21_1041554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 7].length) (baseStart_1041554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1041554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1041554 prefixEnd_1041554 := by exact prefixLift 1041554
  have htrace : WordTrace (prefixWord ++ tailWord_1041554) baseStart_1041554 baseEnd_1041554 := by
    simpa [prefixWord, tailWord_1041554, baseEnd_1041554] using wordTrace_append hprefix tailTrace_1041554
  have hstable : (prefixWord ++ tailWord_1041554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041554).length < 2 ^ (prefixWord ++ tailWord_1041554).sum := by decide
  have hdescent : baseEnd_1041554 < baseStart_1041554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041644 : List Nat := [2, 2, 1, 1, 2, 5, 1, 2, 5]
def baseStart_1041644 : Nat := 118140960795 + 1041644 * 2 ^ 59
def prefixEnd_1041644 : Nat := 4983230072969 + 3 ^ 40 * 1041644 * 2
def baseEnd_1041644 : Nat := 237717352387567909670921

theorem tailTrace_1041644 : CollatzResearch.WordTrace tailWord_1041644 prefixEnd_1041644 237717352387567909670921 := by
  unfold tailWord_1041644
  simp only [CollatzResearch.WordTrace]
  refine ⟨18995938919154580738537993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25327918558872774318050657 18995938919154580738537993)
  ·
    refine ⟨14246954189365935553903495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18995938919154580738537993 14246954189365935553903495)
    ·
      refine ⟨21370431284048903330855243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14246954189365935553903495 21370431284048903330855243)
      ·
        refine ⟨32055646926073354996282865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21370431284048903330855243 32055646926073354996282865)
        ·
          refine ⟨24041735194555016247212149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32055646926073354996282865 24041735194555016247212149)
          ·
            refine ⟨2253912674489532773176139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24041735194555016247212149 2253912674489532773176139)
            ·
              refine ⟨3380869011734299159764209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2253912674489532773176139 3380869011734299159764209)
              ·
                refine ⟨2535651758800724369823157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3380869011734299159764209 2535651758800724369823157)
                ·
                  refine ⟨237717352387567909670921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2535651758800724369823157 237717352387567909670921)
                  ·
                    rfl

theorem cell21_1041644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_1041644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1041644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1041644 prefixEnd_1041644 := by exact prefixLift 1041644
  have htrace : WordTrace (prefixWord ++ tailWord_1041644) baseStart_1041644 baseEnd_1041644 := by
    simpa [prefixWord, tailWord_1041644, baseEnd_1041644] using wordTrace_append hprefix tailTrace_1041644
  have hstable : (prefixWord ++ tailWord_1041644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041644).length < 2 ^ (prefixWord ++ tailWord_1041644).sum := by decide
  have hdescent : baseEnd_1041644 < baseStart_1041644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041658 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 6]
def baseStart_1041658 : Nat := 118140960795 + 1041658 * 2 ^ 59
def prefixEnd_1041658 : Nat := 4983230072969 + 3 ^ 40 * 1041658 * 2
def baseEnd_1041658 : Nat := 237720547378306996437559

theorem tailTrace_1041658 : CollatzResearch.WordTrace tailWord_1041658 prefixEnd_1041658 237720547378306996437559 := by
  unfold tailWord_1041658
  simp only [CollatzResearch.WordTrace]
  refine ⟨9498097115064610467021407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25328258973505627912057085 9498097115064610467021407)
  ·
    refine ⟨14247145672596915700532111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9498097115064610467021407 14247145672596915700532111)
    ·
      refine ⟨21370718508895373550798167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14247145672596915700532111 21370718508895373550798167)
      ·
        refine ⟨32056077763343060326197251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21370718508895373550798167 32056077763343060326197251)
        ·
          refine ⟨48084116645014590489295877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32056077763343060326197251 48084116645014590489295877)
          ·
            refine ⟨9015771870940235716742977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48084116645014590489295877 9015771870940235716742977)
            ·
              refine ⟨6761828903205176787557233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9015771870940235716742977 6761828903205176787557233)
              ·
                refine ⟨5071371677403882590667925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6761828903205176787557233 5071371677403882590667925)
                ·
                  refine ⟨237720547378306996437559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5071371677403882590667925 237720547378306996437559)
                  ·
                    rfl

theorem cell21_1041658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_1041658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1041658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1041658 prefixEnd_1041658 := by exact prefixLift 1041658
  have htrace : WordTrace (prefixWord ++ tailWord_1041658) baseStart_1041658 baseEnd_1041658 := by
    simpa [prefixWord, tailWord_1041658, baseEnd_1041658] using wordTrace_append hprefix tailTrace_1041658
  have hstable : (prefixWord ++ tailWord_1041658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041658).length < 2 ^ (prefixWord ++ tailWord_1041658).sum := by decide
  have hdescent : baseEnd_1041658 < baseStart_1041658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041675 : List Nat := [1, 1, 1, 1, 5, 3, 3, 2, 4]
def baseStart_1041675 : Nat := 118140960795 + 1041675 * 2 ^ 59
def prefixEnd_1041675 : Nat := 4983230072969 + 3 ^ 40 * 1041675 * 2
def baseEnd_1041675 : Nat := 237724427009918744654191

theorem tailTrace_1041675 : CollatzResearch.WordTrace tailWord_1041675 prefixEnd_1041675 237724427009918744654191 := by
  unfold tailWord_1041675
  simp only [CollatzResearch.WordTrace]
  refine ⟨37993008501196853771454479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25328672334131235847636319 37993008501196853771454479)
  ·
    refine ⟨56989512751795280657181719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37993008501196853771454479 56989512751795280657181719)
    ·
      refine ⟨85484269127692920985772579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56989512751795280657181719 85484269127692920985772579)
      ·
        refine ⟨128226403691539381478658869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85484269127692920985772579 128226403691539381478658869)
        ·
          refine ⟨12021225346081817013624269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128226403691539381478658869 12021225346081817013624269)
          ·
            refine ⟨4507959504780681380109101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12021225346081817013624269 4507959504780681380109101)
            ·
              refine ⟨1690484814292755517540913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4507959504780681380109101 1690484814292755517540913)
              ·
                refine ⟨1267863610719566638155685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1690484814292755517540913 1267863610719566638155685)
                ·
                  refine ⟨237724427009918744654191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1267863610719566638155685 237724427009918744654191)
                  ·
                    rfl

theorem cell21_1041675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 4].length) (baseStart_1041675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1041675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1041675 prefixEnd_1041675 := by exact prefixLift 1041675
  have htrace : WordTrace (prefixWord ++ tailWord_1041675) baseStart_1041675 baseEnd_1041675 := by
    simpa [prefixWord, tailWord_1041675, baseEnd_1041675] using wordTrace_append hprefix tailTrace_1041675
  have hstable : (prefixWord ++ tailWord_1041675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041675).length < 2 ^ (prefixWord ++ tailWord_1041675).sum := by decide
  have hdescent : baseEnd_1041675 < baseStart_1041675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041706 : List Nat := [3, 1, 4, 2, 1, 2, 1, 7]
def baseStart_1041706 : Nat := 118140960795 + 1041706 * 2 ^ 59
def prefixEnd_1041706 : Nat := 4983230072969 + 3 ^ 40 * 1041706 * 2
def baseEnd_1041706 : Nat := 79243833877423193212487

theorem tailTrace_1041706 : CollatzResearch.WordTrace tailWord_1041706 prefixEnd_1041706 79243833877423193212487 := by
  unfold tailWord_1041706
  simp only [CollatzResearch.WordTrace]
  refine ⟨9498534791021136516458243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25329426109389697377221981 9498534791021136516458243)
  ·
    refine ⟨14247802186531704774687365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9498534791021136516458243 14247802186531704774687365)
    ·
      refine ⟨2671462909974694645253881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14247802186531704774687365 2671462909974694645253881)
      ·
        refine ⟨2003597182481020983940411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2671462909974694645253881 2003597182481020983940411)
        ·
          refine ⟨3005395773721531475910617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003597182481020983940411 3005395773721531475910617)
          ·
            refine ⟨2254046830291148606932963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3005395773721531475910617 2254046830291148606932963)
            ·
              refine ⟨3381070245436722910399445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2254046830291148606932963 3381070245436722910399445)
              ·
                refine ⟨79243833877423193212487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3381070245436722910399445 79243833877423193212487)
                ·
                  rfl

theorem cell21_1041706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_1041706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1041706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1041706 prefixEnd_1041706 := by exact prefixLift 1041706
  have htrace : WordTrace (prefixWord ++ tailWord_1041706) baseStart_1041706 baseEnd_1041706 := by
    simpa [prefixWord, tailWord_1041706, baseEnd_1041706] using wordTrace_append hprefix tailTrace_1041706
  have hstable : (prefixWord ++ tailWord_1041706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041706).length < 2 ^ (prefixWord ++ tailWord_1041706).sum := by decide
  have hdescent : baseEnd_1041706 < baseStart_1041706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041751 : List Nat := [1, 1, 3, 2, 3, 3, 1, 3, 4]
def baseStart_1041751 : Nat := 118140960795 + 1041751 * 2 ^ 59
def prefixEnd_1041751 : Nat := 4983230072969 + 3 ^ 40 * 1041751 * 2
def baseEnd_1041751 : Nat := 237741771245359501387369

theorem tailTrace_1041751 : CollatzResearch.WordTrace tailWord_1041751 prefixEnd_1041751 237741771245359501387369 := by
  unfold tailWord_1041751
  simp only [CollatzResearch.WordTrace]
  refine ⟨37995780448921518751221107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25330520299281012500814071 37995780448921518751221107)
  ·
    refine ⟨56993670673382278126831661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37995780448921518751221107 56993670673382278126831661)
    ·
      refine ⟨21372626502518354297561873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56993670673382278126831661 21372626502518354297561873)
      ·
        refine ⟨16029469876888765723171405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21372626502518354297561873 16029469876888765723171405)
        ·
          refine ⟨6011051203833287146189277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16029469876888765723171405 6011051203833287146189277)
          ·
            refine ⟨2254144201437482679820979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6011051203833287146189277 2254144201437482679820979)
            ·
              refine ⟨3381216302156224019731469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2254144201437482679820979 3381216302156224019731469)
              ·
                refine ⟨1267956113308584007399301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3381216302156224019731469 1267956113308584007399301)
                ·
                  refine ⟨237741771245359501387369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1267956113308584007399301 237741771245359501387369)
                  ·
                    rfl

theorem cell21_1041751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 4].length) (baseStart_1041751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1041751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1041751 prefixEnd_1041751 := by exact prefixLift 1041751
  have htrace : WordTrace (prefixWord ++ tailWord_1041751) baseStart_1041751 baseEnd_1041751 := by
    simpa [prefixWord, tailWord_1041751, baseEnd_1041751] using wordTrace_append hprefix tailTrace_1041751
  have hstable : (prefixWord ++ tailWord_1041751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041751).length < 2 ^ (prefixWord ++ tailWord_1041751).sum := by decide
  have hdescent : baseEnd_1041751 < baseStart_1041751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041889 : List Nat := [1, 2, 3, 1, 2, 3, 3, 3, 3]
def baseStart_1041889 : Nat := 118140960795 + 1041889 * 2 ^ 59
def prefixEnd_1041889 : Nat := 4983230072969 + 3 ^ 40 * 1041889 * 2
def baseEnd_1041889 : Nat := 237773264725501928087087

theorem tailTrace_1041889 : CollatzResearch.WordTrace tailWord_1041889 prefixEnd_1041889 237773264725501928087087 := by
  unfold tailWord_1041889
  simp only [CollatzResearch.WordTrace]
  refine ⟨38000813722421568319744721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25333875814947712213163147 38000813722421568319744721)
  ·
    refine ⟨28500610291816176239808541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38000813722421568319744721 28500610291816176239808541)
    ·
      refine ⟨10687728859431066089928203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28500610291816176239808541 10687728859431066089928203)
      ·
        refine ⟨16031593289146599134892305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10687728859431066089928203 16031593289146599134892305)
        ·
          refine ⟨12023694966859949351169229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16031593289146599134892305 12023694966859949351169229)
          ·
            refine ⟨4508885612572481006688461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12023694966859949351169229 4508885612572481006688461)
            ·
              refine ⟨1690832104714680377508173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4508885612572481006688461 1690832104714680377508173)
              ·
                refine ⟨634062039268005141565565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1690832104714680377508173 634062039268005141565565)
                ·
                  refine ⟨237773264725501928087087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 634062039268005141565565 237773264725501928087087)
                  ·
                    rfl

theorem cell21_1041889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 3].length) (baseStart_1041889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1041889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1041889 prefixEnd_1041889 := by exact prefixLift 1041889
  have htrace : WordTrace (prefixWord ++ tailWord_1041889) baseStart_1041889 baseEnd_1041889 := by
    simpa [prefixWord, tailWord_1041889, baseEnd_1041889] using wordTrace_append hprefix tailTrace_1041889
  have hstable : (prefixWord ++ tailWord_1041889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041889).length < 2 ^ (prefixWord ++ tailWord_1041889).sum := by decide
  have hdescent : baseEnd_1041889 < baseStart_1041889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041917 : List Nat := [1, 4, 1, 1, 1, 5, 2, 6]
def baseStart_1041917 : Nat := 118140960795 + 1041917 * 2 ^ 59
def prefixEnd_1041917 : Nat := 4983230072969 + 3 ^ 40 * 1041917 * 2
def baseEnd_1041917 : Nat := 79259884902326700540121

theorem tailTrace_1041917 : CollatzResearch.WordTrace tailWord_1041917 prefixEnd_1041917 79259884902326700540121 := by
  unfold tailWord_1041917
  simp only [CollatzResearch.WordTrace]
  refine ⟨38001834966320129101764005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25334556644213419401176003 38001834966320129101764005)
  ·
    refine ⟨7125344056185024206580751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38001834966320129101764005 7125344056185024206580751)
    ·
      refine ⟨10688016084277536309871127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7125344056185024206580751 10688016084277536309871127)
      ·
        refine ⟨16032024126416304464806691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10688016084277536309871127 16032024126416304464806691)
        ·
          refine ⟨24048036189624456697210037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16032024126416304464806691 24048036189624456697210037)
          ·
            refine ⟨2254503392777292815363441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24048036189624456697210037 2254503392777292815363441)
            ·
              refine ⟨1690877544582969611522581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2254503392777292815363441 1690877544582969611522581)
              ·
                refine ⟨79259884902326700540121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1690877544582969611522581 79259884902326700540121)
                ·
                  rfl

theorem cell21_1041917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 6].length) (baseStart_1041917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1041917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1041917 prefixEnd_1041917 := by exact prefixLift 1041917
  have htrace : WordTrace (prefixWord ++ tailWord_1041917) baseStart_1041917 baseEnd_1041917 := by
    simpa [prefixWord, tailWord_1041917, baseEnd_1041917] using wordTrace_append hprefix tailTrace_1041917
  have hstable : (prefixWord ++ tailWord_1041917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041917).length < 2 ^ (prefixWord ++ tailWord_1041917).sum := by decide
  have hdescent : baseEnd_1041917 < baseStart_1041917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042024 : List Nat := [2, 1, 4, 3, 1, 1, 1, 3, 5]
def baseStart_1042024 : Nat := 118140960795 + 1042024 * 2 ^ 59
def prefixEnd_1042024 : Nat := 4983230072969 + 3 ^ 40 * 1042024 * 2
def baseEnd_1042024 : Nat := 237804073564771693336811

theorem tailTrace_1042024 : CollatzResearch.WordTrace tailWord_1042024 prefixEnd_1042024 237804073564771693336811 := by
  unfold tailWord_1042024
  simp only [CollatzResearch.WordTrace]
  refine ⟨19002868788466243187954563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25337158384621657583939417 19002868788466243187954563)
  ·
    refine ⟨28504303182699364781931845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19002868788466243187954563 28504303182699364781931845)
    ·
      refine ⟨5344556846756130896612221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28504303182699364781931845 5344556846756130896612221)
      ·
        refine ⟨2004208817533549086229583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5344556846756130896612221 2004208817533549086229583)
        ·
          refine ⟨3006313226300323629344375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2004208817533549086229583 3006313226300323629344375)
          ·
            refine ⟨4509469839450485444016563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3006313226300323629344375 4509469839450485444016563)
            ·
              refine ⟨6764204759175728166024845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4509469839450485444016563 6764204759175728166024845)
              ·
                refine ⟨2536576784690898062259317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6764204759175728166024845 2536576784690898062259317)
                ·
                  refine ⟨237804073564771693336811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2536576784690898062259317 237804073564771693336811)
                  ·
                    rfl

theorem cell21_1042024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_1042024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042024 prefixEnd_1042024 := by exact prefixLift 1042024
  have htrace : WordTrace (prefixWord ++ tailWord_1042024) baseStart_1042024 baseEnd_1042024 := by
    simpa [prefixWord, tailWord_1042024, baseEnd_1042024] using wordTrace_append hprefix tailTrace_1042024
  have hstable : (prefixWord ++ tailWord_1042024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042024).length < 2 ^ (prefixWord ++ tailWord_1042024).sum := by decide
  have hdescent : baseEnd_1042024 < baseStart_1042024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042058 : List Nat := [3, 1, 2, 3, 2, 3, 1, 3, 3]
def baseStart_1042058 : Nat := 118140960795 + 1042058 * 2 ^ 59
def prefixEnd_1042058 : Nat := 4983230072969 + 3 ^ 40 * 1042058 * 2
def baseEnd_1042058 : Nat := 237811832827995189770075

theorem tailTrace_1042058 : CollatzResearch.WordTrace tailWord_1042058 prefixEnd_1042058 237811832827995189770075 := by
  unfold tailWord_1042058
  simp only [CollatzResearch.WordTrace]
  refine ⟨9501744414702327545661707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25337985105872873455097885 9501744414702327545661707)
  ·
    refine ⟨14252616622053491318492561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9501744414702327545661707 14252616622053491318492561)
    ·
      refine ⟨10689462466540118488869421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14252616622053491318492561 10689462466540118488869421)
      ·
        refine ⟨4008548424952544433326033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10689462466540118488869421 4008548424952544433326033)
        ·
          refine ⟨3006411318714408324994525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4008548424952544433326033 3006411318714408324994525)
          ·
            refine ⟨1127404244517903121872947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3006411318714408324994525 1127404244517903121872947)
            ·
              refine ⟨1691106366776854682809421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127404244517903121872947 1691106366776854682809421)
              ·
                refine ⟨634164887541320506053533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1691106366776854682809421 634164887541320506053533)
                ·
                  refine ⟨237811832827995189770075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 634164887541320506053533 237811832827995189770075)
                  ·
                    rfl

theorem cell21_1042058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_1042058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042058 prefixEnd_1042058 := by exact prefixLift 1042058
  have htrace : WordTrace (prefixWord ++ tailWord_1042058) baseStart_1042058 baseEnd_1042058 := by
    simpa [prefixWord, tailWord_1042058, baseEnd_1042058] using wordTrace_append hprefix tailTrace_1042058
  have hstable : (prefixWord ++ tailWord_1042058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042058).length < 2 ^ (prefixWord ++ tailWord_1042058).sum := by decide
  have hdescent : baseEnd_1042058 < baseStart_1042058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042159 : List Nat := [1, 1, 2, 1, 5, 1, 3, 2, 5]
def baseStart_1042159 : Nat := 118140960795 + 1042159 * 2 ^ 59
def prefixEnd_1042159 : Nat := 4983230072969 + 3 ^ 40 * 1042159 * 2
def baseEnd_1042159 : Nat := 237834882404041458586535

theorem tailTrace_1042159 : CollatzResearch.WordTrace tailWord_1042159 prefixEnd_1042159 237834882404041458586535 := by
  unfold tailWord_1042159
  simp only [CollatzResearch.WordTrace]
  refine ⟨38010661431443404432073531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25340440954295602954715687 38010661431443404432073531)
  ·
    refine ⟨57015992147165106648110297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38010661431443404432073531 57015992147165106648110297)
    ·
      refine ⟨42761994110373829986082723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57015992147165106648110297 42761994110373829986082723)
      ·
        refine ⟨64142991165560744979124085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42761994110373829986082723 64142991165560744979124085)
        ·
          refine ⟨6013405421771319841792883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64142991165560744979124085 6013405421771319841792883)
          ·
            refine ⟨9020108132656979762689325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6013405421771319841792883 9020108132656979762689325)
            ·
              refine ⟨3382540549746367411008497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9020108132656979762689325 3382540549746367411008497)
              ·
                refine ⟨2536905412309775558256373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3382540549746367411008497 2536905412309775558256373)
                ·
                  refine ⟨237834882404041458586535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2536905412309775558256373 237834882404041458586535)
                  ·
                    rfl

theorem cell21_1042159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 5].length) (baseStart_1042159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042159 prefixEnd_1042159 := by exact prefixLift 1042159
  have htrace : WordTrace (prefixWord ++ tailWord_1042159) baseStart_1042159 baseEnd_1042159 := by
    simpa [prefixWord, tailWord_1042159, baseEnd_1042159] using wordTrace_append hprefix tailTrace_1042159
  have hstable : (prefixWord ++ tailWord_1042159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042159).length < 2 ^ (prefixWord ++ tailWord_1042159).sum := by decide
  have hdescent : baseEnd_1042159 < baseStart_1042159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042204 : List Nat := [2, 2, 3, 1, 1, 2, 2, 8]
def baseStart_1042204 : Nat := 118140960795 + 1042204 * 2 ^ 59
def prefixEnd_1042204 : Nat := 4983230072969 + 3 ^ 40 * 1042204 * 2
def baseEnd_1042204 : Nat := 79281717339043793445481

theorem tailTrace_1042204 : CollatzResearch.WordTrace tailWord_1042204 prefixEnd_1042204 79281717339043793445481 := by
  unfold tailWord_1042204
  simp only [CollatzResearch.WordTrace]
  refine ⟨19006151358140188558730833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25341535144186918078307777 19006151358140188558730833)
  ·
    refine ⟨14254613518605141419048125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19006151358140188558730833 14254613518605141419048125)
    ·
      refine ⟨5345480069476928032143047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14254613518605141419048125 5345480069476928032143047)
      ·
        refine ⟨8018220104215392048214571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5345480069476928032143047 8018220104215392048214571)
        ·
          refine ⟨12027330156323088072321857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8018220104215392048214571 12027330156323088072321857)
          ·
            refine ⟨9020497617242316054241393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12027330156323088072321857 9020497617242316054241393)
            ·
              refine ⟨6765373212931737040681045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9020497617242316054241393 6765373212931737040681045)
              ·
                refine ⟨79281717339043793445481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6765373212931737040681045 79281717339043793445481)
                ·
                  rfl

theorem cell21_1042204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 8].length) (baseStart_1042204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042204 prefixEnd_1042204 := by exact prefixLift 1042204
  have htrace : WordTrace (prefixWord ++ tailWord_1042204) baseStart_1042204 baseEnd_1042204 := by
    simpa [prefixWord, tailWord_1042204, baseEnd_1042204] using wordTrace_append hprefix tailTrace_1042204
  have hstable : (prefixWord ++ tailWord_1042204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042204).length < 2 ^ (prefixWord ++ tailWord_1042204).sum := by decide
  have hdescent : baseEnd_1042204 < baseStart_1042204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042207 : List Nat := [1, 1, 2, 4, 2, 1, 5, 1, 4]
def baseStart_1042207 : Nat := 118140960795 + 1042207 * 2 ^ 59
def prefixEnd_1042207 : Nat := 4983230072969 + 3 ^ 40 * 1042207 * 2
def baseEnd_1042207 : Nat := 237845836658004041786437

theorem tailTrace_1042207 : CollatzResearch.WordTrace tailWord_1042207 prefixEnd_1042207 237845836658004041786437 := by
  unfold tailWord_1042207
  simp only [CollatzResearch.WordTrace]
  refine ⟨38012412135269508629820875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25341608090179672419880583 38012412135269508629820875)
  ·
    refine ⟨57018618202904262944731313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38012412135269508629820875 57018618202904262944731313)
    ·
      refine ⟨42763963652178197208548485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57018618202904262944731313 42763963652178197208548485)
      ·
        refine ⟨8018243184783411976602841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42763963652178197208548485 8018243184783411976602841)
        ·
          refine ⟨6013682388587558982452131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8018243184783411976602841 6013682388587558982452131)
          ·
            refine ⟨9020523582881338473678197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6013682388587558982452131 9020523582881338473678197)
            ·
              refine ⟨845674085895125481907331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9020523582881338473678197 845674085895125481907331)
              ·
                refine ⟨1268511128842688222860997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 845674085895125481907331 1268511128842688222860997)
                ·
                  refine ⟨237845836658004041786437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1268511128842688222860997 237845836658004041786437)
                  ·
                    rfl

theorem cell21_1042207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 4].length) (baseStart_1042207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042207 prefixEnd_1042207 := by exact prefixLift 1042207
  have htrace : WordTrace (prefixWord ++ tailWord_1042207) baseStart_1042207 baseEnd_1042207 := by
    simpa [prefixWord, tailWord_1042207, baseEnd_1042207] using wordTrace_append hprefix tailTrace_1042207
  have hstable : (prefixWord ++ tailWord_1042207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042207).length < 2 ^ (prefixWord ++ tailWord_1042207).sum := by decide
  have hdescent : baseEnd_1042207 < baseStart_1042207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042249 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 6]
def baseStart_1042249 : Nat := 118140960795 + 1042249 * 2 ^ 59
def prefixEnd_1042249 : Nat := 4983230072969 + 3 ^ 40 * 1042249 * 2
def baseEnd_1042249 : Nat := 237855421630221302086351

theorem tailTrace_1042249 : CollatzResearch.WordTrace tailWord_1042249 prefixEnd_1042249 237855421630221302086351 := by
  unfold tailWord_1042249
  simp only [CollatzResearch.WordTrace]
  refine ⟨38013944001117349802849801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25342629334078233201899867 38013944001117349802849801)
  ·
    refine ⟨28510458000838012352137351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38013944001117349802849801 28510458000838012352137351)
    ·
      refine ⟨42765687001257018528206027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28510458000838012352137351 42765687001257018528206027)
      ·
        refine ⟨64148530501885527792309041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42765687001257018528206027 64148530501885527792309041)
        ·
          refine ⟨48111397876414145844231781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64148530501885527792309041 48111397876414145844231781)
          ·
            refine ⟨9020887101827652345793459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48111397876414145844231781 9020887101827652345793459)
            ·
              refine ⟨13531330652741478518690189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9020887101827652345793459 13531330652741478518690189)
              ·
                refine ⟨5074248994778054444508821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13531330652741478518690189 5074248994778054444508821)
                ·
                  refine ⟨237855421630221302086351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5074248994778054444508821 237855421630221302086351)
                  ·
                    rfl

theorem cell21_1042249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_1042249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042249 prefixEnd_1042249 := by exact prefixLift 1042249
  have htrace : WordTrace (prefixWord ++ tailWord_1042249) baseStart_1042249 baseEnd_1042249 := by
    simpa [prefixWord, tailWord_1042249, baseEnd_1042249] using wordTrace_append hprefix tailTrace_1042249
  have hstable : (prefixWord ++ tailWord_1042249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042249).length < 2 ^ (prefixWord ++ tailWord_1042249).sum := by decide
  have hdescent : baseEnd_1042249 < baseStart_1042249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042266 : List Nat := [3, 1, 1, 2, 1, 3, 3, 3, 4]
def baseStart_1042266 : Nat := 118140960795 + 1042266 * 2 ^ 59
def prefixEnd_1042266 : Nat := 4983230072969 + 3 ^ 40 * 1042266 * 2
def baseEnd_1042266 : Nat := 237859301261833050302983

theorem tailTrace_1042266 : CollatzResearch.WordTrace tailWord_1042266 prefixEnd_1042266 237859301261833050302983 := by
  unfold tailWord_1042266
  simp only [CollatzResearch.WordTrace]
  refine ⟨9503641010513940426554663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25343042694703841137479101 9503641010513940426554663)
  ·
    refine ⟨14255461515770910639831995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9503641010513940426554663 14255461515770910639831995)
    ·
      refine ⟨21383192273656365959747993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14255461515770910639831995 21383192273656365959747993)
      ·
        refine ⟨16037394205242274469810995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21383192273656365959747993 16037394205242274469810995)
        ·
          refine ⟨24056091307863411704716493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16037394205242274469810995 24056091307863411704716493)
          ·
            refine ⟨9021034240448779389268685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24056091307863411704716493 9021034240448779389268685)
            ·
              refine ⟨3382887840168292270975757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9021034240448779389268685 3382887840168292270975757)
              ·
                refine ⟨1268582940063109601615909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3382887840168292270975757 1268582940063109601615909)
                ·
                  refine ⟨237859301261833050302983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1268582940063109601615909 237859301261833050302983)
                  ·
                    rfl

theorem cell21_1042266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_1042266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042266 prefixEnd_1042266 := by exact prefixLift 1042266
  have htrace : WordTrace (prefixWord ++ tailWord_1042266) baseStart_1042266 baseEnd_1042266 := by
    simpa [prefixWord, tailWord_1042266, baseEnd_1042266] using wordTrace_append hprefix tailTrace_1042266
  have hstable : (prefixWord ++ tailWord_1042266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042266).length < 2 ^ (prefixWord ++ tailWord_1042266).sum := by decide
  have hdescent : baseEnd_1042266 < baseStart_1042266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042280 : List Nat := [2, 1, 4, 2, 1, 1, 1, 9]
def baseStart_1042280 : Nat := 118140960795 + 1042280 * 2 ^ 59
def prefixEnd_1042280 : Nat := 4983230072969 + 3 ^ 40 * 1042280 * 2
def baseEnd_1042280 : Nat := 79287498750857379023207

theorem tailTrace_1042280 : CollatzResearch.WordTrace tailWord_1042280 prefixEnd_1042280 79287498750857379023207 := by
  unfold tailWord_1042280
  simp only [CollatzResearch.WordTrace]
  refine ⟨19007537332002521048614147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25343383109336694731485529 19007537332002521048614147)
  ·
    refine ⟨28511305998003781572921221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19007537332002521048614147 28511305998003781572921221)
    ·
      refine ⟨5345869874625709044922729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28511305998003781572921221 5345869874625709044922729)
      ·
        refine ⟨4009402405969281783692047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5345869874625709044922729 4009402405969281783692047)
        ·
          refine ⟨6014103608953922675538071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4009402405969281783692047 6014103608953922675538071)
          ·
            refine ⟨9021155413430884013307107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6014103608953922675538071 9021155413430884013307107)
            ·
              refine ⟨13531733120146326019960661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9021155413430884013307107 13531733120146326019960661)
              ·
                refine ⟨79287498750857379023207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13531733120146326019960661 79287498750857379023207)
                ·
                  rfl

theorem cell21_1042280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 9].length) (baseStart_1042280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042280 prefixEnd_1042280 := by exact prefixLift 1042280
  have htrace : WordTrace (prefixWord ++ tailWord_1042280) baseStart_1042280 baseEnd_1042280 := by
    simpa [prefixWord, tailWord_1042280, baseEnd_1042280] using wordTrace_append hprefix tailTrace_1042280
  have hstable : (prefixWord ++ tailWord_1042280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042280).length < 2 ^ (prefixWord ++ tailWord_1042280).sum := by decide
  have hdescent : baseEnd_1042280 < baseStart_1042280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042314 : List Nat := [3, 1, 2, 4, 2, 2, 1, 6]
def baseStart_1042314 : Nat := 118140960795 + 1042314 * 2 ^ 59
def prefixEnd_1042314 : Nat := 4983230072969 + 3 ^ 40 * 1042314 * 2
def baseEnd_1042314 : Nat := 79290085171931877834295

theorem tailTrace_1042314 : CollatzResearch.WordTrace tailWord_1042314 prefixEnd_1042314 79290085171931877834295 := by
  unfold tailWord_1042314
  simp only [CollatzResearch.WordTrace]
  refine ⟨9504078686470466475991499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25344209830587910602643997 9504078686470466475991499)
  ·
    refine ⟨14256118029705699713987249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9504078686470466475991499 14256118029705699713987249)
    ·
      refine ⟨10692088522279274785490437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14256118029705699713987249 10692088522279274785490437)
      ·
        refine ⟨2004766597927364022279457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10692088522279274785490437 2004766597927364022279457)
        ·
          refine ⟨1503574948445523016709593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2004766597927364022279457 1503574948445523016709593)
          ·
            refine ⟨1127681211334142262532195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1503574948445523016709593 1127681211334142262532195)
            ·
              refine ⟨1691521817001213393798293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127681211334142262532195 1691521817001213393798293)
              ·
                refine ⟨79290085171931877834295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1691521817001213393798293 79290085171931877834295)
                ·
                  rfl

theorem cell21_1042314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_1042314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042314 prefixEnd_1042314 := by exact prefixLift 1042314
  have htrace : WordTrace (prefixWord ++ tailWord_1042314) baseStart_1042314 baseEnd_1042314 := by
    simpa [prefixWord, tailWord_1042314, baseEnd_1042314] using wordTrace_append hprefix tailTrace_1042314
  have hstable : (prefixWord ++ tailWord_1042314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042314).length < 2 ^ (prefixWord ++ tailWord_1042314).sum := by decide
  have hdescent : baseEnd_1042314 < baseStart_1042314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042390 : List Nat := [5, 2, 1, 1, 3, 1, 1, 7]
def baseStart_1042390 : Nat := 118140960795 + 1042390 * 2 ^ 59
def prefixEnd_1042390 : Nat := 4983230072969 + 3 ^ 40 * 1042390 * 2
def baseEnd_1042390 : Nat := 79295866583745463412021

theorem tailTrace_1042390 : CollatzResearch.WordTrace tailWord_1042390 prefixEnd_1042390 79295866583745463412021 := by
  unfold tailWord_1042390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2376192918350408180233289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25346057795737687255821749 2376192918350408180233289)
  ·
    refine ⟨1782144688762806135174967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2376192918350408180233289 1782144688762806135174967)
    ·
      refine ⟨2673217033144209202762451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1782144688762806135174967 2673217033144209202762451)
      ·
        refine ⟨4009825549716313804143677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2673217033144209202762451 4009825549716313804143677)
        ·
          refine ⟨1503684581143617676553879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4009825549716313804143677 1503684581143617676553879)
          ·
            refine ⟨2255526871715426514830819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503684581143617676553879 2255526871715426514830819)
            ·
              refine ⟨3383290307573139772246229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255526871715426514830819 3383290307573139772246229)
              ·
                refine ⟨79295866583745463412021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3383290307573139772246229 79295866583745463412021)
                ·
                  rfl

theorem cell21_1042390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_1042390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042390 prefixEnd_1042390 := by exact prefixLift 1042390
  have htrace : WordTrace (prefixWord ++ tailWord_1042390) baseStart_1042390 baseEnd_1042390 := by
    simpa [prefixWord, tailWord_1042390, baseEnd_1042390] using wordTrace_append hprefix tailTrace_1042390
  have hstable : (prefixWord ++ tailWord_1042390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042390).length < 2 ^ (prefixWord ++ tailWord_1042390).sum := by decide
  have hdescent : baseEnd_1042390 < baseStart_1042390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042396 : List Nat := [2, 2, 6, 1, 1, 2, 1, 3, 3]
def baseStart_1042396 : Nat := 118140960795 + 1042396 * 2 ^ 59
def prefixEnd_1042396 : Nat := 4983230072969 + 3 ^ 40 * 1042396 * 2
def baseEnd_1042396 : Nat := 237888969032981713136051

theorem tailTrace_1042396 : CollatzResearch.WordTrace tailWord_1042396 prefixEnd_1042396 237888969032981713136051 := by
  unfold tailWord_1042396
  simp only [CollatzResearch.WordTrace]
  refine ⟨19009652765792396954225521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25346203687723195938967361 19009652765792396954225521)
  ·
    refine ⟨14257239574344297715669141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19009652765792396954225521 14257239574344297715669141)
    ·
      refine ⟨668308105047388955421991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14257239574344297715669141 668308105047388955421991)
      ·
        refine ⟨1002462157571083433132987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668308105047388955421991 1002462157571083433132987)
        ·
          refine ⟨1503693236356625149699481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1002462157571083433132987 1503693236356625149699481)
          ·
            refine ⟨1127769927267468862274611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1503693236356625149699481 1127769927267468862274611)
            ·
              refine ⟨1691654890901203293411917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127769927267468862274611 1691654890901203293411917)
              ·
                refine ⟨634370584087951235029469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1691654890901203293411917 634370584087951235029469)
                ·
                  refine ⟨237888969032981713136051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 634370584087951235029469 237888969032981713136051)
                  ·
                    rfl

theorem cell21_1042396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_1042396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042396 prefixEnd_1042396 := by exact prefixLift 1042396
  have htrace : WordTrace (prefixWord ++ tailWord_1042396) baseStart_1042396 baseEnd_1042396 := by
    simpa [prefixWord, tailWord_1042396, baseEnd_1042396] using wordTrace_append hprefix tailTrace_1042396
  have hstable : (prefixWord ++ tailWord_1042396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042396).length < 2 ^ (prefixWord ++ tailWord_1042396).sum := by decide
  have hdescent : baseEnd_1042396 < baseStart_1042396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042401 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 6]
def baseStart_1042401 : Nat := 118140960795 + 1042401 * 2 ^ 59
def prefixEnd_1042401 : Nat := 4983230072969 + 3 ^ 40 * 1042401 * 2
def baseEnd_1042401 : Nat := 237890110101102815552707

theorem tailTrace_1042401 : CollatzResearch.WordTrace tailWord_1042401 prefixEnd_1042401 237890110101102815552707 := by
  unfold tailWord_1042401
  simp only [CollatzResearch.WordTrace]
  refine ⟨38019487896566679762383057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25346325264377786508255371 38019487896566679762383057)
  ·
    refine ⟨28514615922425009821787293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38019487896566679762383057 28514615922425009821787293)
    ·
      refine ⟨10692980970909378683170235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28514615922425009821787293 10692980970909378683170235)
      ·
        refine ⟨16039471456364068024755353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10692980970909378683170235 16039471456364068024755353)
        ·
          refine ⟨12029603592273051018566515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16039471456364068024755353 12029603592273051018566515)
          ·
            refine ⟨18044405388409576527849773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12029603592273051018566515 18044405388409576527849773)
            ·
              refine ⟨6766652020653591197943665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18044405388409576527849773 6766652020653591197943665)
              ·
                refine ⟨5074989015490193398457749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6766652020653591197943665 5074989015490193398457749)
                ·
                  refine ⟨237890110101102815552707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5074989015490193398457749 237890110101102815552707)
                  ·
                    rfl

theorem cell21_1042401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_1042401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042401 prefixEnd_1042401 := by exact prefixLift 1042401
  have htrace : WordTrace (prefixWord ++ tailWord_1042401) baseStart_1042401 baseEnd_1042401 := by
    simpa [prefixWord, tailWord_1042401, baseEnd_1042401] using wordTrace_append hprefix tailTrace_1042401
  have hstable : (prefixWord ++ tailWord_1042401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042401).length < 2 ^ (prefixWord ++ tailWord_1042401).sum := by decide
  have hdescent : baseEnd_1042401 < baseStart_1042401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042472 : List Nat := [2, 1, 5, 3, 2, 1, 2, 2, 3]
def baseStart_1042472 : Nat := 118140960795 + 1042472 * 2 ^ 59
def prefixEnd_1042472 : Nat := 4983230072969 + 3 ^ 40 * 1042472 * 2
def baseEnd_1042472 : Nat := 237906313268422469869229

theorem tailTrace_1042472 : CollatzResearch.WordTrace tailWord_1042472 prefixEnd_1042472 237906313268422469869229 := by
  unfold tailWord_1042472
  simp only [CollatzResearch.WordTrace]
  refine ⟨19011038739654729444108835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25348051652872972592145113 19011038739654729444108835)
  ·
    refine ⟨28516558109482094166163253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19011038739654729444108835 28516558109482094166163253)
    ·
      refine ⟨2673427322763946328077805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28516558109482094166163253 2673427322763946328077805)
      ·
        refine ⟨1002535246036479873029177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2673427322763946328077805 1002535246036479873029177)
        ·
          refine ⟨751901434527359904771883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1002535246036479873029177 751901434527359904771883)
          ·
            refine ⟨1127852151791039857157825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751901434527359904771883 1127852151791039857157825)
            ·
              refine ⟨845889113843279892868369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1127852151791039857157825 845889113843279892868369)
              ·
                refine ⟨634416835382459919651277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 845889113843279892868369 634416835382459919651277)
                ·
                  refine ⟨237906313268422469869229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 634416835382459919651277 237906313268422469869229)
                  ·
                    rfl

theorem cell21_1042472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 3].length) (baseStart_1042472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042472 prefixEnd_1042472 := by exact prefixLift 1042472
  have htrace : WordTrace (prefixWord ++ tailWord_1042472) baseStart_1042472 baseEnd_1042472 := by
    simpa [prefixWord, tailWord_1042472, baseEnd_1042472] using wordTrace_append hprefix tailTrace_1042472
  have hstable : (prefixWord ++ tailWord_1042472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042472).length < 2 ^ (prefixWord ++ tailWord_1042472).sum := by decide
  have hdescent : baseEnd_1042472 < baseStart_1042472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042480 : List Nat := [2, 1, 1, 1, 2, 6, 1, 4, 3]
def baseStart_1042480 : Nat := 118140960795 + 1042480 * 2 ^ 59
def prefixEnd_1042480 : Nat := 4983230072969 + 3 ^ 40 * 1042480 * 2
def baseEnd_1042480 : Nat := 237908138977416233735879

theorem tailTrace_1042480 : CollatzResearch.WordTrace tailWord_1042480 prefixEnd_1042480 237908138977416233735879 := by
  unfold tailWord_1042480
  simp only [CollatzResearch.WordTrace]
  refine ⟨19011184631640238127254447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25348246175520317503005929 19011184631640238127254447)
  ·
    refine ⟨28516776947460357190881671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19011184631640238127254447 28516776947460357190881671)
    ·
      refine ⟨42775165421190535786322507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28516776947460357190881671 42775165421190535786322507)
      ·
        refine ⟨64162748131785803679483761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42775165421190535786322507 64162748131785803679483761)
        ·
          refine ⟨48122061098839352759612821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64162748131785803679483761 48122061098839352759612821)
          ·
            refine ⟨2255721614008094660606851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48122061098839352759612821 2255721614008094660606851)
            ·
              refine ⟨3383582421012141990910277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255721614008094660606851 3383582421012141990910277)
              ·
                refine ⟨634421703939776623295677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3383582421012141990910277 634421703939776623295677)
                ·
                  refine ⟨237908138977416233735879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 634421703939776623295677 237908138977416233735879)
                  ·
                    rfl

theorem cell21_1042480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 3].length) (baseStart_1042480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042480 prefixEnd_1042480 := by exact prefixLift 1042480
  have htrace : WordTrace (prefixWord ++ tailWord_1042480) baseStart_1042480 baseEnd_1042480 := by
    simpa [prefixWord, tailWord_1042480, baseEnd_1042480] using wordTrace_append hprefix tailTrace_1042480
  have hstable : (prefixWord ++ tailWord_1042480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042480).length < 2 ^ (prefixWord ++ tailWord_1042480).sum := by decide
  have hdescent : baseEnd_1042480 < baseStart_1042480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042522 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 7]
def baseStart_1042522 : Nat := 118140960795 + 1042522 * 2 ^ 59
def prefixEnd_1042522 : Nat := 4983230072969 + 3 ^ 40 * 1042522 * 2
def baseEnd_1042522 : Nat := 237917723949633494035793

theorem tailTrace_1042522 : CollatzResearch.WordTrace tailWord_1042522 prefixEnd_1042522 237917723949633494035793 := by
  unfold tailWord_1042522
  simp only [CollatzResearch.WordTrace]
  refine ⟨9505975282282079356884455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25349267419418878285025213 9505975282282079356884455)
  ·
    refine ⟨14258962923423119035326683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9505975282282079356884455 14258962923423119035326683)
    ·
      refine ⟨21388444385134678552990025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14258962923423119035326683 21388444385134678552990025)
      ·
        refine ⟨16041333288851008914742519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21388444385134678552990025 16041333288851008914742519)
        ·
          refine ⟨24061999933276513372113779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16041333288851008914742519 24061999933276513372113779)
          ·
            refine ⟨36092999899914770058170669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24061999933276513372113779 36092999899914770058170669)
            ·
              refine ⟨13534874962468038771814001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36092999899914770058170669 13534874962468038771814001)
              ·
                refine ⟨10151156221851029078860501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13534874962468038771814001 10151156221851029078860501)
                ·
                  refine ⟨237917723949633494035793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10151156221851029078860501 237917723949633494035793)
                  ·
                    rfl

theorem cell21_1042522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_1042522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042522 prefixEnd_1042522 := by exact prefixLift 1042522
  have htrace : WordTrace (prefixWord ++ tailWord_1042522) baseStart_1042522 baseEnd_1042522 := by
    simpa [prefixWord, tailWord_1042522, baseEnd_1042522] using wordTrace_append hprefix tailTrace_1042522
  have hstable : (prefixWord ++ tailWord_1042522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042522).length < 2 ^ (prefixWord ++ tailWord_1042522).sum := by decide
  have hdescent : baseEnd_1042522 < baseStart_1042522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042525 : List Nat := [1, 4, 4, 1, 1, 2, 8]
def baseStart_1042525 : Nat := 118140960795 + 1042525 * 2 ^ 59
def prefixEnd_1042525 : Nat := 4983230072969 + 3 ^ 40 * 1042525 * 2
def baseEnd_1042525 : Nat := 26435378732278461720643

theorem tailTrace_1042525 : CollatzResearch.WordTrace tailWord_1042525 prefixEnd_1042525 26435378732278461720643 := by
  unfold tailWord_1042525
  simp only [CollatzResearch.WordTrace]
  refine ⟨38024010548117448939897029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25349340365411632626598019 38024010548117448939897029)
  ·
    refine ⟨7129501977772021676230693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38024010548117448939897029 7129501977772021676230693)
    ·
      refine ⟨1336781620832254064293255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7129501977772021676230693 1336781620832254064293255)
      ·
        refine ⟨2005172431248381096439883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1336781620832254064293255 2005172431248381096439883)
        ·
          refine ⟨3007758646872571644659825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2005172431248381096439883 3007758646872571644659825)
          ·
            refine ⟨2255818985154428733494869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3007758646872571644659825 2255818985154428733494869)
            ·
              refine ⟨26435378732278461720643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2255818985154428733494869 26435378732278461720643)
              ·
                rfl

theorem cell21_1042525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 8].length) (baseStart_1042525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042525 prefixEnd_1042525 := by exact prefixLift 1042525
  have htrace : WordTrace (prefixWord ++ tailWord_1042525) baseStart_1042525 baseEnd_1042525 := by
    simpa [prefixWord, tailWord_1042525, baseEnd_1042525] using wordTrace_append hprefix tailTrace_1042525
  have hstable : (prefixWord ++ tailWord_1042525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042525).length < 2 ^ (prefixWord ++ tailWord_1042525).sum := by decide
  have hdescent : baseEnd_1042525 < baseStart_1042525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042590 : List Nat := [4, 3, 1, 1, 4, 1, 1, 1, 5]
def baseStart_1042590 : Nat := 118140960795 + 1042590 * 2 ^ 59
def prefixEnd_1042590 : Nat := 4983230072969 + 3 ^ 40 * 1042590 * 2
def baseEnd_1042590 : Nat := 237933242476080486902321

theorem tailTrace_1042590 : CollatzResearch.WordTrace tailWord_1042590 prefixEnd_1042590 237933242476080486902321 := by
  unfold tailWord_1042590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4753297661610245630126653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25350920861921310027342149 4753297661610245630126653)
  ·
    refine ⟨1782486623103842111297495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4753297661610245630126653 1782486623103842111297495)
    ·
      refine ⟨2673729934655763166946243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1782486623103842111297495 2673729934655763166946243)
      ·
        refine ⟨4010594901983644750419365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2673729934655763166946243 4010594901983644750419365)
        ·
          refine ⟨751986544121933390703631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4010594901983644750419365 751986544121933390703631)
          ·
            refine ⟨1127979816182900086055447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751986544121933390703631 1127979816182900086055447)
            ·
              refine ⟨1691969724274350129083171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127979816182900086055447 1691969724274350129083171)
              ·
                refine ⟨2537954586411525193624757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691969724274350129083171 2537954586411525193624757)
                ·
                  refine ⟨237933242476080486902321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2537954586411525193624757 237933242476080486902321)
                  ·
                    rfl

theorem cell21_1042590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_1042590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042590 prefixEnd_1042590 := by exact prefixLift 1042590
  have htrace : WordTrace (prefixWord ++ tailWord_1042590) baseStart_1042590 baseEnd_1042590 := by
    simpa [prefixWord, tailWord_1042590, baseEnd_1042590] using wordTrace_append hprefix tailTrace_1042590
  have hstable : (prefixWord ++ tailWord_1042590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042590).length < 2 ^ (prefixWord ++ tailWord_1042590).sum := by decide
  have hdescent : baseEnd_1042590 < baseStart_1042590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042705 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 6]
def baseStart_1042705 : Nat := 118140960795 + 1042705 * 2 ^ 59
def prefixEnd_1042705 : Nat := 4983230072969 + 3 ^ 40 * 1042705 * 2
def baseEnd_1042705 : Nat := 237959487042865842485419

theorem tailTrace_1042705 : CollatzResearch.WordTrace tailWord_1042705 prefixEnd_1042705 237959487042865842485419 := by
  unfold tailWord_1042705
  simp only [CollatzResearch.WordTrace]
  refine ⟨38030575687465339681449569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25353717124976893120966379 38030575687465339681449569)
  ·
    refine ⟨28522931765599004761087177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38030575687465339681449569 28522931765599004761087177)
    ·
      refine ⟨21392198824199253570815383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28522931765599004761087177 21392198824199253570815383)
      ·
        refine ⟨32088298236298880356223075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21392198824199253570815383 32088298236298880356223075)
        ·
          refine ⟨48132447354448320534334613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32088298236298880356223075 48132447354448320534334613)
          ·
            refine ⟨2256208469739765025046935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48132447354448320534334613 2256208469739765025046935)
            ·
              refine ⟨3384312704609647537570403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2256208469739765025046935 3384312704609647537570403)
              ·
                refine ⟨5076469056914471306355605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3384312704609647537570403 5076469056914471306355605)
                ·
                  refine ⟨237959487042865842485419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5076469056914471306355605 237959487042865842485419)
                  ·
                    rfl

theorem cell21_1042705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_1042705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042705 prefixEnd_1042705 := by exact prefixLift 1042705
  have htrace : WordTrace (prefixWord ++ tailWord_1042705) baseStart_1042705 baseEnd_1042705 := by
    simpa [prefixWord, tailWord_1042705, baseEnd_1042705] using wordTrace_append hprefix tailTrace_1042705
  have hstable : (prefixWord ++ tailWord_1042705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042705).length < 2 ^ (prefixWord ++ tailWord_1042705).sum := by decide
  have hdescent : baseEnd_1042705 < baseStart_1042705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042753 : List Nat := [1, 2, 5, 2, 2, 2, 7]
def baseStart_1042753 : Nat := 118140960795 + 1042753 * 2 ^ 59
def prefixEnd_1042753 : Nat := 4983230072969 + 3 ^ 40 * 1042753 * 2
def baseEnd_1042753 : Nat := 26441160144092047298369

theorem tailTrace_1042753 : CollatzResearch.WordTrace tailWord_1042753 prefixEnd_1042753 26441160144092047298369 := by
  unfold tailWord_1042753
  simp only [CollatzResearch.WordTrace]
  refine ⟨38032326391291443879196913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25354884260860962586131275 38032326391291443879196913)
  ·
    refine ⟨28524244793468582909397685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38032326391291443879196913 28524244793468582909397685)
    ·
      refine ⟨2674147949387679647756033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28524244793468582909397685 2674147949387679647756033)
      ·
        refine ⟨2005610962040759735817025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2674147949387679647756033 2005610962040759735817025)
        ·
          refine ⟨1504208221530569801862769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2005610962040759735817025 1504208221530569801862769)
          ·
            refine ⟨1128156166147927351397077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1504208221530569801862769 1128156166147927351397077)
            ·
              refine ⟨26441160144092047298369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1128156166147927351397077 26441160144092047298369)
              ·
                rfl

theorem cell21_1042753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 7].length) (baseStart_1042753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042753 prefixEnd_1042753 := by exact prefixLift 1042753
  have htrace : WordTrace (prefixWord ++ tailWord_1042753) baseStart_1042753 baseEnd_1042753 := by
    simpa [prefixWord, tailWord_1042753, baseEnd_1042753] using wordTrace_append hprefix tailTrace_1042753
  have hstable : (prefixWord ++ tailWord_1042753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042753).length < 2 ^ (prefixWord ++ tailWord_1042753).sum := by decide
  have hdescent : baseEnd_1042753 < baseStart_1042753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042818 : List Nat := [3, 4, 2, 1, 2, 1, 1, 4, 3]
def baseStart_1042818 : Nat := 118140960795 + 1042818 * 2 ^ 59
def prefixEnd_1042818 : Nat := 4983230072969 + 3 ^ 40 * 1042818 * 2
def baseEnd_1042818 : Nat := 237985275182402757101855

theorem tailTrace_1042818 : CollatzResearch.WordTrace tailWord_1042818 prefixEnd_1042818 237985275182402757101855 := by
  unfold tailWord_1042818
  simp only [CollatzResearch.WordTrace]
  refine ⟨9508674284013989995078277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25356464757370639986875405 9508674284013989995078277)
  ·
    refine ⟨1782876428252623124077177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9508674284013989995078277 1782876428252623124077177)
    ·
      refine ⟨1337157321189467343057883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1782876428252623124077177 1337157321189467343057883)
      ·
        refine ⟨2005735981784201014586825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1337157321189467343057883 2005735981784201014586825)
        ·
          refine ⟨1504301986338150760940119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2005735981784201014586825 1504301986338150760940119)
          ·
            refine ⟨2256452979507226141410179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504301986338150760940119 2256452979507226141410179)
            ·
              refine ⟨3384679469260839212115269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2256452979507226141410179 3384679469260839212115269)
              ·
                refine ⟨634627400486407352271613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3384679469260839212115269 634627400486407352271613)
                ·
                  refine ⟨237985275182402757101855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 634627400486407352271613 237985275182402757101855)
                  ·
                    rfl

theorem cell21_1042818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_1042818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042818 prefixEnd_1042818 := by exact prefixLift 1042818
  have htrace : WordTrace (prefixWord ++ tailWord_1042818) baseStart_1042818 baseEnd_1042818 := by
    simpa [prefixWord, tailWord_1042818, baseEnd_1042818] using wordTrace_append hprefix tailTrace_1042818
  have hstable : (prefixWord ++ tailWord_1042818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042818).length < 2 ^ (prefixWord ++ tailWord_1042818).sum := by decide
  have hdescent : baseEnd_1042818 < baseStart_1042818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042846 : List Nat := [4, 3, 1, 2, 1, 2, 3, 5]
def baseStart_1042846 : Nat := 118140960795 + 1042846 * 2 ^ 59
def prefixEnd_1042846 : Nat := 4983230072969 + 3 ^ 40 * 1042846 * 2
def baseEnd_1042846 : Nat := 79330555054626976878377

theorem tailTrace_1042846 : CollatzResearch.WordTrace tailWord_1042846 prefixEnd_1042846 79330555054626976878377 := by
  unfold tailWord_1042846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4754464797494315095291549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25357145586636347174888261 4754464797494315095291549)
  ·
    refine ⟨1782924299060368160734331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4754464797494315095291549 1782924299060368160734331)
    ·
      refine ⟨2674386448590552241101497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1782924299060368160734331 2674386448590552241101497)
      ·
        refine ⟨2005789836442914180826123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2674386448590552241101497 2005789836442914180826123)
        ·
          refine ⟨3008684754664371271239185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2005789836442914180826123 3008684754664371271239185)
          ·
            refine ⟨2256513565998278453429389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3008684754664371271239185 2256513565998278453429389)
            ·
              refine ⟨846192587249354420036021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2256513565998278453429389 846192587249354420036021)
              ·
                refine ⟨79330555054626976878377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 846192587249354420036021 79330555054626976878377)
                ·
                  rfl

theorem cell21_1042846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_1042846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042846 prefixEnd_1042846 := by exact prefixLift 1042846
  have htrace : WordTrace (prefixWord ++ tailWord_1042846) baseStart_1042846 baseEnd_1042846 := by
    simpa [prefixWord, tailWord_1042846, baseEnd_1042846] using wordTrace_append hprefix tailTrace_1042846
  have hstable : (prefixWord ++ tailWord_1042846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042846).length < 2 ^ (prefixWord ++ tailWord_1042846).sum := by decide
  have hdescent : baseEnd_1042846 < baseStart_1042846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042871 : List Nat := [1, 1, 3, 1, 3, 4, 8]
def baseStart_1042871 : Nat := 118140960795 + 1042871 * 2 ^ 59
def prefixEnd_1042871 : Nat := 4983230072969 + 3 ^ 40 * 1042871 * 2
def baseEnd_1042871 : Nat := 26444152278276271413157

theorem tailTrace_1042871 : CollatzResearch.WordTrace tailWord_1042871 prefixEnd_1042871 26444152278276271413157 := by
  unfold tailWord_1042871
  simp only [CollatzResearch.WordTrace]
  refine ⟨38036630204863950031992467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25357753469909300021328311 38036630204863950031992467)
  ·
    refine ⟨57054945307295925047988701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38036630204863950031992467 57054945307295925047988701)
    ·
      refine ⟨21395604490235971892995763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57054945307295925047988701 21395604490235971892995763)
      ·
        refine ⟨32093406735353957839493645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21395604490235971892995763 32093406735353957839493645)
        ·
          refine ⟨12035027525757734189810117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32093406735353957839493645 12035027525757734189810117)
          ·
            refine ⟨2256567661079575160589397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12035027525757734189810117 2256567661079575160589397)
            ·
              refine ⟨26444152278276271413157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2256567661079575160589397 26444152278276271413157)
              ·
                rfl

theorem cell21_1042871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 8].length) (baseStart_1042871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042871 prefixEnd_1042871 := by exact prefixLift 1042871
  have htrace : WordTrace (prefixWord ++ tailWord_1042871) baseStart_1042871 baseEnd_1042871 := by
    simpa [prefixWord, tailWord_1042871, baseEnd_1042871] using wordTrace_append hprefix tailTrace_1042871
  have hstable : (prefixWord ++ tailWord_1042871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042871).length < 2 ^ (prefixWord ++ tailWord_1042871).sum := by decide
  have hdescent : baseEnd_1042871 < baseStart_1042871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042936 : List Nat := [2, 1, 2, 1, 1, 4, 5, 2, 3]
def baseStart_1042936 : Nat := 118140960795 + 1042936 * 2 ^ 59
def prefixEnd_1042936 : Nat := 4983230072969 + 3 ^ 40 * 1042936 * 2
def baseEnd_1042936 : Nat := 238012204390060774134947

theorem tailTrace_1042936 : CollatzResearch.WordTrace tailWord_1042936 prefixEnd_1042936 238012204390060774134947 := by
  unfold tailWord_1042936
  simp only [CollatzResearch.WordTrace]
  refine ⟨19019500474814233066554331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25359333966418977422072441 19019500474814233066554331)
  ·
    refine ⟨28529250712221349599831497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19019500474814233066554331 28529250712221349599831497)
    ·
      refine ⟨21396938034166012199873623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28529250712221349599831497 21396938034166012199873623)
      ·
        refine ⟨32095407051249018299810435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21396938034166012199873623 32095407051249018299810435)
        ·
          refine ⟨48143110576873527449715653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32095407051249018299810435 48143110576873527449715653)
          ·
            refine ⟨9026833233163786396821685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48143110576873527449715653 9026833233163786396821685)
            ·
              refine ⟨846265615609104974702033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9026833233163786396821685 846265615609104974702033)
              ·
                refine ⟨634699211706828731026525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 846265615609104974702033 634699211706828731026525)
                ·
                  refine ⟨238012204390060774134947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 634699211706828731026525 238012204390060774134947)
                  ·
                    rfl

theorem cell21_1042936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 3].length) (baseStart_1042936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042936 prefixEnd_1042936 := by exact prefixLift 1042936
  have htrace : WordTrace (prefixWord ++ tailWord_1042936) baseStart_1042936 baseEnd_1042936 := by
    simpa [prefixWord, tailWord_1042936, baseEnd_1042936] using wordTrace_append hprefix tailTrace_1042936
  have hstable : (prefixWord ++ tailWord_1042936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042936).length < 2 ^ (prefixWord ++ tailWord_1042936).sum := by decide
  have hdescent : baseEnd_1042936 < baseStart_1042936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042947 : List Nat := [1, 1, 1, 3, 2, 1, 6, 6]
def baseStart_1042947 : Nat := 118140960795 + 1042947 * 2 ^ 59
def prefixEnd_1042947 : Nat := 4983230072969 + 3 ^ 40 * 1042947 * 2
def baseEnd_1042947 : Nat := 79338238246642399817197

theorem tailTrace_1042947 : CollatzResearch.WordTrace tailWord_1042947 prefixEnd_1042947 79338238246642399817197 := by
  unfold tailWord_1042947
  simp only [CollatzResearch.WordTrace]
  refine ⟨38039402152588615011759095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25359601435059076674506063 38039402152588615011759095)
  ·
    refine ⟨57059103228882922517638643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38039402152588615011759095 57059103228882922517638643)
    ·
      refine ⟨85588654843324383776457965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57059103228882922517638643 85588654843324383776457965)
      ·
        refine ⟨32095745566246643916171737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85588654843324383776457965 32095745566246643916171737)
        ·
          refine ⟨24071809174684982937128803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32095745566246643916171737 24071809174684982937128803)
          ·
            refine ⟨36107713762027474405693205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24071809174684982937128803 36107713762027474405693205)
            ·
              refine ⟨1692549082595037862766869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36107713762027474405693205 1692549082595037862766869)
              ·
                refine ⟨79338238246642399817197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1692549082595037862766869 79338238246642399817197)
                ·
                  rfl

theorem cell21_1042947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 6].length) (baseStart_1042947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042947 prefixEnd_1042947 := by exact prefixLift 1042947
  have htrace : WordTrace (prefixWord ++ tailWord_1042947) baseStart_1042947 baseEnd_1042947 := by
    simpa [prefixWord, tailWord_1042947, baseEnd_1042947] using wordTrace_append hprefix tailTrace_1042947
  have hstable : (prefixWord ++ tailWord_1042947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042947).length < 2 ^ (prefixWord ++ tailWord_1042947).sum := by decide
  have hdescent : baseEnd_1042947 < baseStart_1042947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042992 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 6]
def baseStart_1042992 : Nat := 118140960795 + 1042992 * 2 ^ 59
def prefixEnd_1042992 : Nat := 4983230072969 + 3 ^ 40 * 1042992 * 2
def baseEnd_1042992 : Nat := 238024984353017121201499

theorem tailTrace_1042992 : CollatzResearch.WordTrace tailWord_1042992 prefixEnd_1042992 238024984353017121201499 := by
  unfold tailWord_1042992
  simp only [CollatzResearch.WordTrace]
  refine ⟨19020521718712793848573615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25360695624950391798098153 19020521718712793848573615)
  ·
    refine ⟨28530782578069190772860423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19020521718712793848573615 28530782578069190772860423)
    ·
      refine ⟨42796173867103786159290635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28530782578069190772860423 42796173867103786159290635)
      ·
        refine ⟨64194260800655679238935953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42796173867103786159290635 64194260800655679238935953)
        ·
          refine ⟨48145695600491759429201965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64194260800655679238935953 48145695600491759429201965)
          ·
            refine ⟨18054635850184409785950737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48145695600491759429201965 18054635850184409785950737)
            ·
              refine ⟨13540976887638307339463053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18054635850184409785950737 13540976887638307339463053)
              ·
                refine ⟨5077866332864365252298645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13540976887638307339463053 5077866332864365252298645)
                ·
                  refine ⟨238024984353017121201499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5077866332864365252298645 238024984353017121201499)
                  ·
                    rfl

theorem cell21_1042992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_1042992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042992 prefixEnd_1042992 := by exact prefixLift 1042992
  have htrace : WordTrace (prefixWord ++ tailWord_1042992) baseStart_1042992 baseEnd_1042992 := by
    simpa [prefixWord, tailWord_1042992, baseEnd_1042992] using wordTrace_append hprefix tailTrace_1042992
  have hstable : (prefixWord ++ tailWord_1042992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042992).length < 2 ^ (prefixWord ++ tailWord_1042992).sum := by decide
  have hdescent : baseEnd_1042992 < baseStart_1042992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042995 : List Nat := [1, 1, 1, 2, 4, 2, 3, 4, 3]
def baseStart_1042995 : Nat := 118140960795 + 1042995 * 2 ^ 59
def prefixEnd_1042995 : Nat := 4983230072969 + 3 ^ 40 * 1042995 * 2
def baseEnd_1042995 : Nat := 238025668993889782651493

theorem tailTrace_1042995 : CollatzResearch.WordTrace tailWord_1042995 prefixEnd_1042995 238025668993889782651493 := by
  unfold tailWord_1042995
  simp only [CollatzResearch.WordTrace]
  refine ⟨38041152856414719209506439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25360768570943146139670959 38041152856414719209506439)
  ·
    refine ⟨57061729284622078814259659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38041152856414719209506439 57061729284622078814259659)
    ·
      refine ⟨85592593926933118221389489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57061729284622078814259659 85592593926933118221389489)
      ·
        refine ⟨64194445445199838666042117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85592593926933118221389489 64194445445199838666042117)
        ·
          refine ⟨12036458520974969749882897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64194445445199838666042117 12036458520974969749882897)
          ·
            refine ⟨9027343890731227312412173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12036458520974969749882897 9027343890731227312412173)
            ·
              refine ⟨3385253959024210242154565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9027343890731227312412173 3385253959024210242154565)
              ·
                refine ⟨634735117317039420403981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3385253959024210242154565 634735117317039420403981)
                ·
                  refine ⟨238025668993889782651493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 634735117317039420403981 238025668993889782651493)
                  ·
                    rfl

theorem cell21_1042995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 3].length) (baseStart_1042995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1042995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1042995 prefixEnd_1042995 := by exact prefixLift 1042995
  have htrace : WordTrace (prefixWord ++ tailWord_1042995) baseStart_1042995 baseEnd_1042995 := by
    simpa [prefixWord, tailWord_1042995, baseEnd_1042995] using wordTrace_append hprefix tailTrace_1042995
  have hstable : (prefixWord ++ tailWord_1042995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042995).length < 2 ^ (prefixWord ++ tailWord_1042995).sum := by decide
  have hdescent : baseEnd_1042995 < baseStart_1042995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043102 : List Nat := [4, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_1043102 : Nat := 118140960795 + 1043102 * 2 ^ 59
def prefixEnd_1043102 : Nat := 4983230072969 + 3 ^ 40 * 1043102 * 2
def baseEnd_1043102 : Nat := 238050087851681374367941

theorem tailTrace_1043102 : CollatzResearch.WordTrace tailWord_1043102 prefixEnd_1043102 238050087851681374367941 := by
  unfold tailWord_1043102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4755631933378384560456445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25363370311351384322434373 4755631933378384560456445)
  ·
    refine ⟨1783361975016894210171167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4755631933378384560456445 1783361975016894210171167)
    ·
      refine ⟨2675042962525341315256751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1783361975016894210171167 2675042962525341315256751)
      ·
        refine ⟨4012564443788011972885127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2675042962525341315256751 4012564443788011972885127)
        ·
          refine ⟨6018846665682017959327691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012564443788011972885127 6018846665682017959327691)
          ·
            refine ⟨9028269998523026938991537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6018846665682017959327691 9028269998523026938991537)
            ·
              refine ⟨6771202498892270204243653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9028269998523026938991537 6771202498892270204243653)
              ·
                refine ⟨1269600468542300663295685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6771202498892270204243653 1269600468542300663295685)
                ·
                  refine ⟨238050087851681374367941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1269600468542300663295685 238050087851681374367941)
                  ·
                    rfl

theorem cell21_1043102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_1043102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043102 prefixEnd_1043102 := by exact prefixLift 1043102
  have htrace : WordTrace (prefixWord ++ tailWord_1043102) baseStart_1043102 baseEnd_1043102 := by
    simpa [prefixWord, tailWord_1043102, baseEnd_1043102] using wordTrace_append hprefix tailTrace_1043102
  have hstable : (prefixWord ++ tailWord_1043102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043102).length < 2 ^ (prefixWord ++ tailWord_1043102).sum := by decide
  have hdescent : baseEnd_1043102 < baseStart_1043102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043105 : List Nat := [1, 2, 3, 3, 3, 1, 3, 2, 3]
def baseStart_1043105 : Nat := 118140960795 + 1043105 * 2 ^ 59
def prefixEnd_1043105 : Nat := 4983230072969 + 3 ^ 40 * 1043105 * 2
def baseEnd_1043105 : Nat := 238050772492554035817935

theorem tailTrace_1043105 : CollatzResearch.WordTrace tailWord_1043105 prefixEnd_1043105 238050772492554035817935 := by
  unfold tailWord_1043105
  simp only [CollatzResearch.WordTrace]
  refine ⟨38045164886016207996010769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25363443257344138664007179 38045164886016207996010769)
  ·
    refine ⟨28533873664512155997008077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38045164886016207996010769 28533873664512155997008077)
    ·
      refine ⟨10700202624192058498878029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28533873664512155997008077 10700202624192058498878029)
      ·
        refine ⟨4012575984072021937079261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10700202624192058498878029 4012575984072021937079261)
        ·
          refine ⟨1504715994027008226404723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4012575984072021937079261 1504715994027008226404723)
          ·
            refine ⟨2257073991040512339607085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504715994027008226404723 2257073991040512339607085)
            ·
              refine ⟨846402746640192127352657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2257073991040512339607085 846402746640192127352657)
              ·
                refine ⟨634802059980144095514493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 846402746640192127352657 634802059980144095514493)
                ·
                  refine ⟨238050772492554035817935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 634802059980144095514493 238050772492554035817935)
                  ·
                    rfl

theorem cell21_1043105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 3].length) (baseStart_1043105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043105 prefixEnd_1043105 := by exact prefixLift 1043105
  have htrace : WordTrace (prefixWord ++ tailWord_1043105) baseStart_1043105 baseEnd_1043105 := by
    simpa [prefixWord, tailWord_1043105, baseEnd_1043105] using wordTrace_append hprefix tailTrace_1043105
  have hstable : (prefixWord ++ tailWord_1043105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043105).length < 2 ^ (prefixWord ++ tailWord_1043105).sum := by decide
  have hdescent : baseEnd_1043105 < baseStart_1043105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043161 : List Nat := [1, 2, 1, 2, 3, 2, 4, 2, 4]
def baseStart_1043161 : Nat := 118140960795 + 1043161 * 2 ^ 59
def prefixEnd_1043161 : Nat := 4983230072969 + 3 ^ 40 * 1043161 * 2
def baseEnd_1043161 : Nat := 238063552455510382884487

theorem tailTrace_1043161 : CollatzResearch.WordTrace tailWord_1043161 prefixEnd_1043161 238063552455510382884487 := by
  unfold tailWord_1043161
  simp only [CollatzResearch.WordTrace]
  refine ⟨38047207373813329560049337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25364804915875553040032891 38047207373813329560049337)
  ·
    refine ⟨28535405530359997170037003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38047207373813329560049337 28535405530359997170037003)
    ·
      refine ⟨42803108295539995755055505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28535405530359997170037003 42803108295539995755055505)
      ·
        refine ⟨32102331221654996816291629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42803108295539995755055505 32102331221654996816291629)
        ·
          refine ⟨12038374208120623806109361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32102331221654996816291629 12038374208120623806109361)
          ·
            refine ⟨9028780656090467854582021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12038374208120623806109361 9028780656090467854582021)
            ·
              refine ⟨1692896373016962722734129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9028780656090467854582021 1692896373016962722734129)
              ·
                refine ⟨1269672279762722042050597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1692896373016962722734129 1269672279762722042050597)
                ·
                  refine ⟨238063552455510382884487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1269672279762722042050597 238063552455510382884487)
                  ·
                    rfl

theorem cell21_1043161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 4].length) (baseStart_1043161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043161 prefixEnd_1043161 := by exact prefixLift 1043161
  have htrace : WordTrace (prefixWord ++ tailWord_1043161) baseStart_1043161 baseEnd_1043161 := by
    simpa [prefixWord, tailWord_1043161, baseEnd_1043161] using wordTrace_append hprefix tailTrace_1043161
  have hstable : (prefixWord ++ tailWord_1043161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043161).length < 2 ^ (prefixWord ++ tailWord_1043161).sum := by decide
  have hdescent : baseEnd_1043161 < baseStart_1043161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043223 : List Nat := [1, 1, 3, 4, 3, 1, 2, 1, 5]
def baseStart_1043223 : Nat := 118140960795 + 1043223 * 2 ^ 59
def prefixEnd_1043223 : Nat := 4983230072969 + 3 ^ 40 * 1043223 * 2
def baseEnd_1043223 : Nat := 238077701700212052851027

theorem tailTrace_1043223 : CollatzResearch.WordTrace tailWord_1043223 prefixEnd_1043223 238077701700212052851027 := by
  unfold tailWord_1043223
  simp only [CollatzResearch.WordTrace]
  refine ⟨38049468699588714148806323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25366312466392476099204215 38049468699588714148806323)
  ·
    refine ⟨57074203049383071223209485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38049468699588714148806323 57074203049383071223209485)
    ·
      refine ⟨21402826143518651708703557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57074203049383071223209485 21402826143518651708703557)
      ·
        refine ⟨4013029901909747195381917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21402826143518651708703557 4013029901909747195381917)
        ·
          refine ⟨1504886213216155198268219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4013029901909747195381917 1504886213216155198268219)
          ·
            refine ⟨2257329319824232797402329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504886213216155198268219 2257329319824232797402329)
            ·
              refine ⟨1692996989868174598051747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2257329319824232797402329 1692996989868174598051747)
              ·
                refine ⟨2539495484802261897077621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1692996989868174598051747 2539495484802261897077621)
                ·
                  refine ⟨238077701700212052851027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2539495484802261897077621 238077701700212052851027)
                  ·
                    rfl

theorem cell21_1043223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 5].length) (baseStart_1043223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043223 prefixEnd_1043223 := by exact prefixLift 1043223
  have htrace : WordTrace (prefixWord ++ tailWord_1043223) baseStart_1043223 baseEnd_1043223 := by
    simpa [prefixWord, tailWord_1043223, baseEnd_1043223] using wordTrace_append hprefix tailTrace_1043223
  have hstable : (prefixWord ++ tailWord_1043223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043223).length < 2 ^ (prefixWord ++ tailWord_1043223).sum := by decide
  have hdescent : baseEnd_1043223 < baseStart_1043223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043251 : List Nat := [1, 1, 1, 2, 6, 2, 1, 7]
def baseStart_1043251 : Nat := 118140960795 + 1043251 * 2 ^ 59
def prefixEnd_1043251 : Nat := 4983230072969 + 3 ^ 40 * 1043251 * 2
def baseEnd_1043251 : Nat := 79361363893896742128101

theorem tailTrace_1043251 : CollatzResearch.WordTrace tailWord_1043251 prefixEnd_1043251 79361363893896742128101 := by
  unfold tailWord_1043251
  simp only [CollatzResearch.WordTrace]
  refine ⟨38050489943487274930825607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25366993295658183287217071 38050489943487274930825607)
  ·
    refine ⟨57075734915230912396238411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38050489943487274930825607 57075734915230912396238411)
    ·
      refine ⟨85613602372846368594357617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57075734915230912396238411 85613602372846368594357617)
      ·
        refine ⟨64210201779634776445768213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85613602372846368594357617 64210201779634776445768213)
        ·
          refine ⟨3009853208420380145895385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64210201779634776445768213 3009853208420380145895385)
          ·
            refine ⟨2257389906315285109421539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3009853208420380145895385 2257389906315285109421539)
            ·
              refine ⟨3386084859472927664132309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2257389906315285109421539 3386084859472927664132309)
              ·
                refine ⟨79361363893896742128101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3386084859472927664132309 79361363893896742128101)
                ·
                  rfl

theorem cell21_1043251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 7].length) (baseStart_1043251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043251 prefixEnd_1043251 := by exact prefixLift 1043251
  have htrace : WordTrace (prefixWord ++ tailWord_1043251) baseStart_1043251 baseEnd_1043251 := by
    simpa [prefixWord, tailWord_1043251, baseEnd_1043251] using wordTrace_append hprefix tailTrace_1043251
  have hstable : (prefixWord ++ tailWord_1043251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043251).length < 2 ^ (prefixWord ++ tailWord_1043251).sum := by decide
  have hdescent : baseEnd_1043251 < baseStart_1043251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043386 : List Nat := [3, 1, 1, 1, 2, 1, 12]
def baseStart_1043386 : Nat := 118140960795 + 1043386 * 2 ^ 59
def prefixEnd_1043386 : Nat := 4983230072969 + 3 ^ 40 * 1043386 * 2
def baseEnd_1043386 : Nat := 26457211168995554626003

theorem tailTrace_1043386 : CollatzResearch.WordTrace tailWord_1043386 prefixEnd_1043386 26457211168995554626003 := by
  unfold tailWord_1043386
  simp only [CollatzResearch.WordTrace]
  refine ⟨9513853449499548246747503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25370275865332128657993341 9513853449499548246747503)
  ·
    refine ⟨14270780174249322370121255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9513853449499548246747503 14270780174249322370121255)
    ·
      refine ⟨21406170261373983555181883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14270780174249322370121255 21406170261373983555181883)
      ·
        refine ⟨32109255392060975332772825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21406170261373983555181883 32109255392060975332772825)
        ·
          refine ⟨24081941544045731499579619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32109255392060975332772825 24081941544045731499579619)
          ·
            refine ⟨36122912316068597249369429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24081941544045731499579619 36122912316068597249369429)
            ·
              refine ⟨26457211168995554626003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 36122912316068597249369429 26457211168995554626003)
              ·
                rfl

theorem cell21_1043386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 12].length) (baseStart_1043386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043386 prefixEnd_1043386 := by exact prefixLift 1043386
  have htrace : WordTrace (prefixWord ++ tailWord_1043386) baseStart_1043386 baseEnd_1043386 := by
    simpa [prefixWord, tailWord_1043386, baseEnd_1043386] using wordTrace_append hprefix tailTrace_1043386
  have hstable : (prefixWord ++ tailWord_1043386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043386).length < 2 ^ (prefixWord ++ tailWord_1043386).sum := by decide
  have hdescent : baseEnd_1043386 < baseStart_1043386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043389 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 6]
def baseStart_1043389 : Nat := 118140960795 + 1043389 * 2 ^ 59
def prefixEnd_1043389 : Nat := 4983230072969 + 3 ^ 40 * 1043389 * 2
def baseEnd_1043389 : Nat := 238115585161832653084021

theorem tailTrace_1043389 : CollatzResearch.WordTrace tailWord_1043389 prefixEnd_1043389 238115585161832653084021 := by
  unfold tailWord_1043389
  simp only [CollatzResearch.WordTrace]
  refine ⟨38055523216987324499349221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25370348811324882999566147 38055523216987324499349221)
  ·
    refine ⟨7135410603185123343627979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38055523216987324499349221 7135410603185123343627979)
    ·
      refine ⟨10703115904777685015441969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7135410603185123343627979 10703115904777685015441969)
      ·
        refine ⟨8027336928583263761581477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10703115904777685015441969 8027336928583263761581477)
        ·
          refine ⟨1505125674109361955296527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8027336928583263761581477 1505125674109361955296527)
          ·
            refine ⟨2257688511164042932944791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505125674109361955296527 2257688511164042932944791)
            ·
              refine ⟨3386532766746064399417187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2257688511164042932944791 3386532766746064399417187)
              ·
                refine ⟨5079799150119096599125781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386532766746064399417187 5079799150119096599125781)
                ·
                  refine ⟨238115585161832653084021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5079799150119096599125781 238115585161832653084021)
                  ·
                    rfl

theorem cell21_1043389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_1043389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043389 prefixEnd_1043389 := by exact prefixLift 1043389
  have htrace : WordTrace (prefixWord ++ tailWord_1043389) baseStart_1043389 baseEnd_1043389 := by
    simpa [prefixWord, tailWord_1043389, baseEnd_1043389] using wordTrace_append hprefix tailTrace_1043389
  have hstable : (prefixWord ++ tailWord_1043389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043389).length < 2 ^ (prefixWord ++ tailWord_1043389).sum := by decide
  have hdescent : baseEnd_1043389 < baseStart_1043389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043398 : List Nat := [6, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_1043398 : Nat := 118140960795 + 1043398 * 2 ^ 59
def prefixEnd_1043398 : Nat := 4983230072969 + 3 ^ 40 * 1043398 * 2
def baseEnd_1043398 : Nat := 238117639084450637434003

theorem tailTrace_1043398 : CollatzResearch.WordTrace tailWord_1043398 prefixEnd_1043398 238117639084450637434003 := by
  unfold tailWord_1043398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1189245358561084969888339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25370567649303146024284565 1189245358561084969888339)
  ·
    refine ⟨1783868037841627454832509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1189245358561084969888339 1783868037841627454832509)
    ·
      refine ⟨668950514190610295562191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1783868037841627454832509 668950514190610295562191)
      ·
        refine ⟨1003425771285915443343287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668950514190610295562191 1003425771285915443343287)
        ·
          refine ⟨1505138656928873165014931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003425771285915443343287 1505138656928873165014931)
          ·
            refine ⟨2257707985393309747522397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505138656928873165014931 2257707985393309747522397)
            ·
              refine ⟨846640494522491155320899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2257707985393309747522397 846640494522491155320899)
              ·
                refine ⟨1269960741783736732981349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846640494522491155320899 1269960741783736732981349)
                ·
                  refine ⟨238117639084450637434003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1269960741783736732981349 238117639084450637434003)
                  ·
                    rfl

theorem cell21_1043398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_1043398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043398 prefixEnd_1043398 := by exact prefixLift 1043398
  have htrace : WordTrace (prefixWord ++ tailWord_1043398) baseStart_1043398 baseEnd_1043398 := by
    simpa [prefixWord, tailWord_1043398, baseEnd_1043398] using wordTrace_append hprefix tailTrace_1043398
  have hstable : (prefixWord ++ tailWord_1043398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043398).length < 2 ^ (prefixWord ++ tailWord_1043398).sum := by decide
  have hdescent : baseEnd_1043398 < baseStart_1043398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043406 : List Nat := [4, 1, 1, 1, 2, 4, 3, 1, 4]
def baseStart_1043406 : Nat := 118140960795 + 1043406 * 2 ^ 59
def prefixEnd_1043406 : Nat := 4983230072969 + 3 ^ 40 * 1043406 * 2
def baseEnd_1043406 : Nat := 238119464793444401300653

theorem tailTrace_1043406 : CollatzResearch.WordTrace tailWord_1043406 prefixEnd_1043406 238119464793444401300653 := by
  unfold tailWord_1043406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4757017907240717050339759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25370762171950490935145381 4757017907240717050339759)
  ·
    refine ⟨7135526860861075575509639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4757017907240717050339759 7135526860861075575509639)
    ·
      refine ⟨10703290291291613363264459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7135526860861075575509639 10703290291291613363264459)
      ·
        refine ⟨16054935436937420044896689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10703290291291613363264459 16054935436937420044896689)
        ·
          refine ⟨12041201577703065033672517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16054935436937420044896689 12041201577703065033672517)
          ·
            refine ⟨2257725295819324693813597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12041201577703065033672517 2257725295819324693813597)
            ·
              refine ⟨846646985932246760180099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2257725295819324693813597 846646985932246760180099)
              ·
                refine ⟨1269970478898370140270149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846646985932246760180099 1269970478898370140270149)
                ·
                  refine ⟨238119464793444401300653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1269970478898370140270149 238119464793444401300653)
                  ·
                    rfl

theorem cell21_1043406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_1043406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043406 prefixEnd_1043406 := by exact prefixLift 1043406
  have htrace : WordTrace (prefixWord ++ tailWord_1043406) baseStart_1043406 baseEnd_1043406 := by
    simpa [prefixWord, tailWord_1043406, baseEnd_1043406] using wordTrace_append hprefix tailTrace_1043406
  have hstable : (prefixWord ++ tailWord_1043406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043406).length < 2 ^ (prefixWord ++ tailWord_1043406).sum := by decide
  have hdescent : baseEnd_1043406 < baseStart_1043406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043448 : List Nat := [2, 1, 2, 1, 1, 3, 1, 6, 4]
def baseStart_1043448 : Nat := 118140960795 + 1043448 * 2 ^ 59
def prefixEnd_1043448 : Nat := 4983230072969 + 3 ^ 40 * 1043448 * 2
def baseEnd_1043448 : Nat := 238129049765661661600567

theorem tailTrace_1043448 : CollatzResearch.WordTrace tailWord_1043448 prefixEnd_1043448 238129049765661661600567 := by
  unfold tailWord_1043448
  simp only [CollatzResearch.WordTrace]
  refine ⟨19028837561886788787873499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25371783415849051717164665 19028837561886788787873499)
  ·
    refine ⟨28543256342830183181810249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19028837561886788787873499 28543256342830183181810249)
    ·
      refine ⟨21407442257122637386357687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28543256342830183181810249 21407442257122637386357687)
      ·
        refine ⟨32111163385683956079536531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21407442257122637386357687 32111163385683956079536531)
        ·
          refine ⟨48166745078525934119304797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32111163385683956079536531 48166745078525934119304797)
          ·
            refine ⟨18062529404447225294739299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48166745078525934119304797 18062529404447225294739299)
            ·
              refine ⟨27093794106670837942108949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18062529404447225294739299 27093794106670837942108949)
              ·
                refine ⟨1270021598750195528536357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27093794106670837942108949 1270021598750195528536357)
                ·
                  refine ⟨238129049765661661600567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1270021598750195528536357 238129049765661661600567)
                  ·
                    rfl

theorem cell21_1043448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 4].length) (baseStart_1043448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043448 prefixEnd_1043448 := by exact prefixLift 1043448
  have htrace : WordTrace (prefixWord ++ tailWord_1043448) baseStart_1043448 baseEnd_1043448 := by
    simpa [prefixWord, tailWord_1043448, baseEnd_1043448] using wordTrace_append hprefix tailTrace_1043448
  have hstable : (prefixWord ++ tailWord_1043448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043448).length < 2 ^ (prefixWord ++ tailWord_1043448).sum := by decide
  have hdescent : baseEnd_1043448 < baseStart_1043448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043479 : List Nat := [1, 1, 3, 5, 1, 1, 2, 7]
def baseStart_1043479 : Nat := 118140960795 + 1043479 * 2 ^ 59
def prefixEnd_1043479 : Nat := 4983230072969 + 3 ^ 40 * 1043479 * 2
def baseEnd_1043479 : Nat := 79378708129337498861279

theorem tailTrace_1043479 : CollatzResearch.WordTrace tailWord_1043479 prefixEnd_1043479 79378708129337498861279 := by
  unfold tailWord_1043479
  simp only [CollatzResearch.WordTrace]
  refine ⟨38058805786661269870125491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25372537191107513246750327 38058805786661269870125491)
  ·
    refine ⟨57088208679991904805188237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38058805786661269870125491 57088208679991904805188237)
    ·
      refine ⟨21408078254996964301945589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57088208679991904805188237 21408078254996964301945589)
      ·
        refine ⟨2007007336405965403307399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21408078254996964301945589 2007007336405965403307399)
        ·
          refine ⟨3010511004608948104961099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2007007336405965403307399 3010511004608948104961099)
          ·
            refine ⟨4515766506913422157441649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3010511004608948104961099 4515766506913422157441649)
            ·
              refine ⟨3386824880185066618081237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4515766506913422157441649 3386824880185066618081237)
              ·
                refine ⟨79378708129337498861279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3386824880185066618081237 79378708129337498861279)
                ·
                  rfl

theorem cell21_1043479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 7].length) (baseStart_1043479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043479 prefixEnd_1043479 := by exact prefixLift 1043479
  have htrace : WordTrace (prefixWord ++ tailWord_1043479) baseStart_1043479 baseEnd_1043479 := by
    simpa [prefixWord, tailWord_1043479, baseEnd_1043479] using wordTrace_append hprefix tailTrace_1043479
  have hstable : (prefixWord ++ tailWord_1043479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043479).length < 2 ^ (prefixWord ++ tailWord_1043479).sum := by decide
  have hdescent : baseEnd_1043479 < baseStart_1043479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043589 : List Nat := [1, 3, 1, 1, 7, 1, 2, 5]
def baseStart_1043589 : Nat := 118140960795 + 1043589 * 2 ^ 59
def prefixEnd_1043589 : Nat := 4983230072969 + 3 ^ 40 * 1043589 * 2
def baseEnd_1043589 : Nat := 79387075962225583250093

theorem tailTrace_1043589 : CollatzResearch.WordTrace tailWord_1043589 prefixEnd_1043589 79387075962225583250093 := by
  unfold tailWord_1043589
  simp only [CollatzResearch.WordTrace]
  refine ⟨38062817816262758656629821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25375211877508505771086547 38062817816262758656629821)
  ·
    refine ⟨14273556681098534496236183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38062817816262758656629821 14273556681098534496236183)
    ·
      refine ⟨21410335021647801744354275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14273556681098534496236183 21410335021647801744354275)
      ·
        refine ⟨32115502532471702616531413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21410335021647801744354275 32115502532471702616531413)
        ·
          refine ⟨752707090604805530074955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 32115502532471702616531413 752707090604805530074955)
          ·
            refine ⟨1129060635907208295112433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752707090604805530074955 1129060635907208295112433)
            ·
              refine ⟨846795476930406221334325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1129060635907208295112433 846795476930406221334325)
              ·
                refine ⟨79387075962225583250093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 846795476930406221334325 79387075962225583250093)
                ·
                  rfl

theorem cell21_1043589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 5].length) (baseStart_1043589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043589 prefixEnd_1043589 := by exact prefixLift 1043589
  have htrace : WordTrace (prefixWord ++ tailWord_1043589) baseStart_1043589 baseEnd_1043589 := by
    simpa [prefixWord, tailWord_1043589, baseEnd_1043589] using wordTrace_append hprefix tailTrace_1043589
  have hstable : (prefixWord ++ tailWord_1043589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043589).length < 2 ^ (prefixWord ++ tailWord_1043589).sum := by decide
  have hdescent : baseEnd_1043589 < baseStart_1043589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043620 : List Nat := [2, 3, 1, 2, 3, 2, 3, 2, 3]
def baseStart_1043620 : Nat := 118140960795 + 1043620 * 2 ^ 59
def prefixEnd_1043620 : Nat := 4983230072969 + 3 ^ 40 * 1043620 * 2
def baseEnd_1043620 : Nat := 238168302509027584733549

theorem tailTrace_1043620 : CollatzResearch.WordTrace tailWord_1043620 prefixEnd_1043620 238168302509027584733549 := by
  unfold tailWord_1043620
  simp only [CollatzResearch.WordTrace]
  refine ⟨19031974239575225475504157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25375965652766967300672209 19031974239575225475504157)
  ·
    refine ⟨7136990339840709553314059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19031974239575225475504157 7136990339840709553314059)
    ·
      refine ⟨10705485509761064329971089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7136990339840709553314059 10705485509761064329971089)
      ·
        refine ⟨8029114132320798247478317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10705485509761064329971089 8029114132320798247478317)
        ·
          refine ⟨3010917799620299342804369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8029114132320798247478317 3010917799620299342804369)
          ·
            refine ⟨2258188349715224507103277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3010917799620299342804369 2258188349715224507103277)
            ·
              refine ⟨846820631143209190163729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2258188349715224507103277 846820631143209190163729)
              ·
                refine ⟨635115473357406892622797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 846820631143209190163729 635115473357406892622797)
                ·
                  refine ⟨238168302509027584733549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 635115473357406892622797 238168302509027584733549)
                  ·
                    rfl

theorem cell21_1043620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_1043620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043620 prefixEnd_1043620 := by exact prefixLift 1043620
  have htrace : WordTrace (prefixWord ++ tailWord_1043620) baseStart_1043620 baseEnd_1043620 := by
    simpa [prefixWord, tailWord_1043620, baseEnd_1043620] using wordTrace_append hprefix tailTrace_1043620
  have hstable : (prefixWord ++ tailWord_1043620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043620).length < 2 ^ (prefixWord ++ tailWord_1043620).sum := by decide
  have hdescent : baseEnd_1043620 < baseStart_1043620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043634 : List Nat := [3, 2, 1, 1, 1, 6, 2, 1, 4]
def baseStart_1043634 : Nat := 118140960795 + 1043634 * 2 ^ 59
def prefixEnd_1043634 : Nat := 4983230072969 + 3 ^ 40 * 1043634 * 2
def baseEnd_1043634 : Nat := 238171497499766671500187

theorem tailTrace_1043634 : CollatzResearch.WordTrace tailWord_1043634 prefixEnd_1043634 238171497499766671500187 := by
  unfold tailWord_1043634
  simp only [CollatzResearch.WordTrace]
  refine ⟨9516114775274932835504489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25376306067399820894678637 9516114775274932835504489)
  ·
    refine ⟨7137086081456199626628367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9516114775274932835504489 7137086081456199626628367)
    ·
      refine ⟨10705629122184299439942551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7137086081456199626628367 10705629122184299439942551)
      ·
        refine ⟨16058443683276449159913827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10705629122184299439942551 16058443683276449159913827)
        ·
          refine ⟨24087665524914673739870741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16058443683276449159913827 24087665524914673739870741)
          ·
            refine ⟨1129109321480375331556441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24087665524914673739870741 1129109321480375331556441)
            ·
              refine ⟨846831991110281498667331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1129109321480375331556441 846831991110281498667331)
              ·
                refine ⟨1270247986665422248000997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846831991110281498667331 1270247986665422248000997)
                ·
                  refine ⟨238171497499766671500187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1270247986665422248000997 238171497499766671500187)
                  ·
                    rfl

theorem cell21_1043634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_1043634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043634 prefixEnd_1043634 := by exact prefixLift 1043634
  have htrace : WordTrace (prefixWord ++ tailWord_1043634) baseStart_1043634 baseEnd_1043634 := by
    simpa [prefixWord, tailWord_1043634, baseEnd_1043634] using wordTrace_append hprefix tailTrace_1043634
  have hstable : (prefixWord ++ tailWord_1043634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043634).length < 2 ^ (prefixWord ++ tailWord_1043634).sum := by decide
  have hdescent : baseEnd_1043634 < baseStart_1043634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043645 : List Nat := [1, 4, 1, 2, 1, 1, 2, 4, 5]
def baseStart_1043645 : Nat := 118140960795 + 1043645 * 2 ^ 59
def prefixEnd_1043645 : Nat := 4983230072969 + 3 ^ 40 * 1043645 * 2
def baseEnd_1043645 : Nat := 238174007849633096816831

theorem tailTrace_1043645 : CollatzResearch.WordTrace tailWord_1043645 prefixEnd_1043645 238174007849633096816831 := by
  unfold tailWord_1043645
  simp only [CollatzResearch.WordTrace]
  refine ⟨38064860304059880220668389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25376573536039920147112259 38064860304059880220668389)
  ·
    refine ⟨7137161307011227541375323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38064860304059880220668389 7137161307011227541375323)
    ·
      refine ⟨10705741960516841312062985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7137161307011227541375323 10705741960516841312062985)
      ·
        refine ⟨8029306470387630984047239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10705741960516841312062985 8029306470387630984047239)
        ·
          refine ⟨12043959705581446476070859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8029306470387630984047239 12043959705581446476070859)
          ·
            refine ⟨18065939558372169714106289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12043959705581446476070859 18065939558372169714106289)
            ·
              refine ⟨13549454668779127285579717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18065939558372169714106289 13549454668779127285579717)
              ·
                refine ⟨2540522750396086366046197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13549454668779127285579717 2540522750396086366046197)
                ·
                  refine ⟨238174007849633096816831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2540522750396086366046197 238174007849633096816831)
                  ·
                    rfl

theorem cell21_1043645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_1043645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043645 prefixEnd_1043645 := by exact prefixLift 1043645
  have htrace : WordTrace (prefixWord ++ tailWord_1043645) baseStart_1043645 baseEnd_1043645 := by
    simpa [prefixWord, tailWord_1043645, baseEnd_1043645] using wordTrace_append hprefix tailTrace_1043645
  have hstable : (prefixWord ++ tailWord_1043645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043645).length < 2 ^ (prefixWord ++ tailWord_1043645).sum := by decide
  have hdescent : baseEnd_1043645 < baseStart_1043645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043659 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 6]
def baseStart_1043659 : Nat := 118140960795 + 1043659 * 2 ^ 59
def prefixEnd_1043659 : Nat := 4983230072969 + 3 ^ 40 * 1043659 * 2
def baseEnd_1043659 : Nat := 238177202840372183583469

theorem tailTrace_1043659 : CollatzResearch.WordTrace tailWord_1043659 prefixEnd_1043659 238177202840372183583469 := by
  unfold tailWord_1043659
  simp only [CollatzResearch.WordTrace]
  refine ⟨38065370926009160611678031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25376913950672773741118687 38065370926009160611678031)
  ·
    refine ⟨57098056389013740917517047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38065370926009160611678031 57098056389013740917517047)
    ·
      refine ⟨85647084583520611376275571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57098056389013740917517047 85647084583520611376275571)
      ·
        refine ⟨128470626875280917064413357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85647084583520611376275571 128470626875280917064413357)
        ·
          refine ⟨48176485078230343899155009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128470626875280917064413357 48176485078230343899155009)
          ·
            refine ⟨36132363808672757924366257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48176485078230343899155009 36132363808672757924366257)
            ·
              refine ⟨27099272856504568443274693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36132363808672757924366257 27099272856504568443274693)
              ·
                refine ⟨5081113660594606583114005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27099272856504568443274693 5081113660594606583114005)
                ·
                  refine ⟨238177202840372183583469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5081113660594606583114005 238177202840372183583469)
                  ·
                    rfl

theorem cell21_1043659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 6].length) (baseStart_1043659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043659 prefixEnd_1043659 := by exact prefixLift 1043659
  have htrace : WordTrace (prefixWord ++ tailWord_1043659) baseStart_1043659 baseEnd_1043659 := by
    simpa [prefixWord, tailWord_1043659, baseEnd_1043659] using wordTrace_append hprefix tailTrace_1043659
  have hstable : (prefixWord ++ tailWord_1043659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043659).length < 2 ^ (prefixWord ++ tailWord_1043659).sum := by decide
  have hdescent : baseEnd_1043659 < baseStart_1043659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043679 : List Nat := [1, 1, 2, 3, 2, 1, 6, 2, 3]
def baseStart_1043679 : Nat := 118140960795 + 1043679 * 2 ^ 59
def prefixEnd_1043679 : Nat := 4983230072969 + 3 ^ 40 * 1043679 * 2
def baseEnd_1043679 : Nat := 238181767112856593250095

theorem tailTrace_1043679 : CollatzResearch.WordTrace tailWord_1043679 prefixEnd_1043679 238181767112856593250095 := by
  unfold tailWord_1043679
  simp only [CollatzResearch.WordTrace]
  refine ⟨38066100385936704027406091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25377400257291136018270727 38066100385936704027406091)
  ·
    refine ⟨57099150578905056041109137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38066100385936704027406091 57099150578905056041109137)
    ·
      refine ⟨42824362934178792030831853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57099150578905056041109137 42824362934178792030831853)
      ·
        refine ⟨16059136100317047011561945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42824362934178792030831853 16059136100317047011561945)
        ·
          refine ⟨12044352075237785258671459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16059136100317047011561945 12044352075237785258671459)
          ·
            refine ⟨18066528112856677888007189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12044352075237785258671459 18066528112856677888007189)
            ·
              refine ⟨846868505290156776000337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18066528112856677888007189 846868505290156776000337)
              ·
                refine ⟨635151378967617582000253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 846868505290156776000337 635151378967617582000253)
                ·
                  refine ⟨238181767112856593250095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 635151378967617582000253 238181767112856593250095)
                  ·
                    rfl

theorem cell21_1043679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 3].length) (baseStart_1043679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043679 prefixEnd_1043679 := by exact prefixLift 1043679
  have htrace : WordTrace (prefixWord ++ tailWord_1043679) baseStart_1043679 baseEnd_1043679 := by
    simpa [prefixWord, tailWord_1043679, baseEnd_1043679] using wordTrace_append hprefix tailTrace_1043679
  have hstable : (prefixWord ++ tailWord_1043679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043679).length < 2 ^ (prefixWord ++ tailWord_1043679).sum := by decide
  have hdescent : baseEnd_1043679 < baseStart_1043679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043693 : List Nat := [1, 5, 1, 2, 2, 1, 2, 3, 4]
def baseStart_1043693 : Nat := 118140960795 + 1043693 * 2 ^ 59
def prefixEnd_1043693 : Nat := 4983230072969 + 3 ^ 40 * 1043693 * 2
def baseEnd_1043693 : Nat := 238184962103595680016733

theorem tailTrace_1043693 : CollatzResearch.WordTrace tailWord_1043693 prefixEnd_1043693 238184962103595680016733 := by
  unfold tailWord_1043693
  simp only [CollatzResearch.WordTrace]
  refine ⟨38066611007885984418415733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25377740671923989612277155 38066611007885984418415733)
  ·
    refine ⟨3568744781989311039226475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38066611007885984418415733 3568744781989311039226475)
    ·
      refine ⟨5353117172983966558839713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3568744781989311039226475 5353117172983966558839713)
      ·
        refine ⟨4014837879737974919129785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5353117172983966558839713 4014837879737974919129785)
        ·
          refine ⟨3011128409803481189347339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4014837879737974919129785 3011128409803481189347339)
          ·
            refine ⟨4516692614705221784021009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3011128409803481189347339 4516692614705221784021009)
            ·
              refine ⟨3387519461028916338015757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4516692614705221784021009 3387519461028916338015757)
              ·
                refine ⟨1270319797885843626755909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3387519461028916338015757 1270319797885843626755909)
                ·
                  refine ⟨238184962103595680016733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1270319797885843626755909 238184962103595680016733)
                  ·
                    rfl

theorem cell21_1043693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_1043693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043693 prefixEnd_1043693 := by exact prefixLift 1043693
  have htrace : WordTrace (prefixWord ++ tailWord_1043693) baseStart_1043693 baseEnd_1043693 := by
    simpa [prefixWord, tailWord_1043693, baseEnd_1043693] using wordTrace_append hprefix tailTrace_1043693
  have hstable : (prefixWord ++ tailWord_1043693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043693).length < 2 ^ (prefixWord ++ tailWord_1043693).sum := by decide
  have hdescent : baseEnd_1043693 < baseStart_1043693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043738 : List Nat := [3, 1, 1, 3, 3, 2, 2, 1, 5]
def baseStart_1043738 : Nat := 118140960795 + 1043738 * 2 ^ 59
def prefixEnd_1043738 : Nat := 4983230072969 + 3 ^ 40 * 1043738 * 2
def baseEnd_1043738 : Nat := 238195231716685601766641

theorem tailTrace_1043738 : CollatzResearch.WordTrace tailWord_1043738 prefixEnd_1043738 238195231716685601766641 := by
  unfold tailWord_1043738
  simp only [CollatzResearch.WordTrace]
  refine ⟨9517063073180739275950967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25378834861815304735869245 9517063073180739275950967)
  ·
    refine ⟨14275594609771108913926451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9517063073180739275950967 14275594609771108913926451)
    ·
      refine ⟨21413391914656663370889677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14275594609771108913926451 21413391914656663370889677)
      ·
        refine ⟨8030021967996248764083629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21413391914656663370889677 8030021967996248764083629)
        ·
          refine ⟨3011258237998593286531361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8030021967996248764083629 3011258237998593286531361)
          ·
            refine ⟨2258443678498944964898521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3011258237998593286531361 2258443678498944964898521)
            ·
              refine ⟨1693832758874208723673891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2258443678498944964898521 1693832758874208723673891)
              ·
                refine ⟨2540749138311313085510837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1693832758874208723673891 2540749138311313085510837)
                ·
                  refine ⟨238195231716685601766641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2540749138311313085510837 238195231716685601766641)
                  ·
                    rfl

theorem cell21_1043738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_1043738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043738 prefixEnd_1043738 := by exact prefixLift 1043738
  have htrace : WordTrace (prefixWord ++ tailWord_1043738) baseStart_1043738 baseEnd_1043738 := by
    simpa [prefixWord, tailWord_1043738, baseEnd_1043738] using wordTrace_append hprefix tailTrace_1043738
  have hstable : (prefixWord ++ tailWord_1043738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043738).length < 2 ^ (prefixWord ++ tailWord_1043738).sum := by decide
  have hdescent : baseEnd_1043738 < baseStart_1043738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043789 : List Nat := [1, 6, 1, 3, 2, 1, 1, 1, 5]
def baseStart_1043789 : Nat := 118140960795 + 1043789 * 2 ^ 59
def prefixEnd_1043789 : Nat := 4983230072969 + 3 ^ 40 * 1043789 * 2
def baseEnd_1043789 : Nat := 238206870611520846416537

theorem tailTrace_1043789 : CollatzResearch.WordTrace tailWord_1043789 prefixEnd_1043789 238206870611520846416537 := by
  unfold tailWord_1043789
  simp only [CollatzResearch.WordTrace]
  refine ⟨38070112415538192813910421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25380074943692128542606947 38070112415538192813910421)
  ·
    refine ⟨1784536519478352788152051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38070112415538192813910421 1784536519478352788152051)
    ·
      refine ⟨2676804779217529182228077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1784536519478352788152051 2676804779217529182228077)
      ·
        refine ⟨1003801792206573443335529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2676804779217529182228077 1003801792206573443335529)
        ·
          refine ⟨752851344154930082501647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1003801792206573443335529 752851344154930082501647)
          ·
            refine ⟨1129277016232395123752471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752851344154930082501647 1129277016232395123752471)
            ·
              refine ⟨1693915524348592685628707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129277016232395123752471 1693915524348592685628707)
              ·
                refine ⟨2540873286522889028443061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1693915524348592685628707 2540873286522889028443061)
                ·
                  refine ⟨238206870611520846416537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2540873286522889028443061 238206870611520846416537)
                  ·
                    rfl

theorem cell21_1043789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_1043789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043789 prefixEnd_1043789 := by exact prefixLift 1043789
  have htrace : WordTrace (prefixWord ++ tailWord_1043789) baseStart_1043789 baseEnd_1043789 := by
    simpa [prefixWord, tailWord_1043789, baseEnd_1043789] using wordTrace_append hprefix tailTrace_1043789
  have hstable : (prefixWord ++ tailWord_1043789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043789).length < 2 ^ (prefixWord ++ tailWord_1043789).sum := by decide
  have hdescent : baseEnd_1043789 < baseStart_1043789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043848 : List Nat := [2, 1, 3, 3, 1, 4, 2, 2, 3]
def baseStart_1043848 : Nat := 118140960795 + 1043848 * 2 ^ 59
def prefixEnd_1043848 : Nat := 4983230072969 + 3 ^ 40 * 1043848 * 2
def baseEnd_1043848 : Nat := 238220335215349854933083

theorem tailTrace_1043848 : CollatzResearch.WordTrace tailWord_1043848 prefixEnd_1043848 238220335215349854933083 := by
  unfold tailWord_1043848
  simp only [CollatzResearch.WordTrace]
  refine ⟨19036132161162222945154099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25381509548216297260205465 19036132161162222945154099)
  ·
    refine ⟨28554198241743334417731149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19036132161162222945154099 28554198241743334417731149)
    ·
      refine ⟨10707824340653750406649181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28554198241743334417731149 10707824340653750406649181)
      ·
        refine ⟨4015434127745156402493443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10707824340653750406649181 4015434127745156402493443)
        ·
          refine ⟨6023151191617734603740165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4015434127745156402493443 6023151191617734603740165)
          ·
            refine ⟨1129340848428325238201281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6023151191617734603740165 1129340848428325238201281)
            ·
              refine ⟨847005636321243928650961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1129340848428325238201281 847005636321243928650961)
              ·
                refine ⟨635254227240932946488221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847005636321243928650961 635254227240932946488221)
                ·
                  refine ⟨238220335215349854933083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 635254227240932946488221 238220335215349854933083)
                  ·
                    rfl

theorem cell21_1043848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 3].length) (baseStart_1043848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043848 prefixEnd_1043848 := by exact prefixLift 1043848
  have htrace : WordTrace (prefixWord ++ tailWord_1043848) baseStart_1043848 baseEnd_1043848 := by
    simpa [prefixWord, tailWord_1043848, baseEnd_1043848] using wordTrace_append hprefix tailTrace_1043848
  have hstable : (prefixWord ++ tailWord_1043848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043848).length < 2 ^ (prefixWord ++ tailWord_1043848).sum := by decide
  have hdescent : baseEnd_1043848 < baseStart_1043848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043904 : List Nat := [2, 1, 1, 2, 3, 1, 5, 2, 4]
def baseStart_1043904 : Nat := 118140960795 + 1043904 * 2 ^ 59
def prefixEnd_1043904 : Nat := 4983230072969 + 3 ^ 40 * 1043904 * 2
def baseEnd_1043904 : Nat := 238233115178306201999635

theorem tailTrace_1043904 : CollatzResearch.WordTrace tailWord_1043904 prefixEnd_1043904 238233115178306201999635 := by
  unfold tailWord_1043904
  simp only [CollatzResearch.WordTrace]
  refine ⟨19037153405060783727173383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25382871206747711636231177 19037153405060783727173383)
  ·
    refine ⟨28555730107591175590760075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19037153405060783727173383 28555730107591175590760075)
    ·
      refine ⟨42833595161386763386140113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28555730107591175590760075 42833595161386763386140113)
      ·
        refine ⟨32125196371040072539605085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42833595161386763386140113 32125196371040072539605085)
        ·
          refine ⟨12046948639140027202351907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32125196371040072539605085 12046948639140027202351907)
          ·
            refine ⟨18070422958710040803527861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12046948639140027202351907 18070422958710040803527861)
            ·
              refine ⟨1694102152379066325330737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18070422958710040803527861 1694102152379066325330737)
              ·
                refine ⟨1270576614284299743998053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1694102152379066325330737 1270576614284299743998053)
                ·
                  refine ⟨238233115178306201999635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1270576614284299743998053 238233115178306201999635)
                  ·
                    rfl

theorem cell21_1043904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 4].length) (baseStart_1043904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1043904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1043904 prefixEnd_1043904 := by exact prefixLift 1043904
  have htrace : WordTrace (prefixWord ++ tailWord_1043904) baseStart_1043904 baseEnd_1043904 := by
    simpa [prefixWord, tailWord_1043904, baseEnd_1043904] using wordTrace_append hprefix tailTrace_1043904
  have hstable : (prefixWord ++ tailWord_1043904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043904).length < 2 ^ (prefixWord ++ tailWord_1043904).sum := by decide
  have hdescent : baseEnd_1043904 < baseStart_1043904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044028 : List Nat := [2, 2, 2, 2, 5, 1, 1, 6]
def baseStart_1044028 : Nat := 118140960795 + 1044028 * 2 ^ 59
def prefixEnd_1044028 : Nat := 4983230072969 + 3 ^ 40 * 1044028 * 2
def baseEnd_1044028 : Nat := 79420471222569847310905

theorem tailTrace_1044028 : CollatzResearch.WordTrace tailWord_1044028 prefixEnd_1044028 79420471222569847310905 := by
  unfold tailWord_1044028
  simp only [CollatzResearch.WordTrace]
  refine ⟨19039414730836168315930369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25385886307781557754573825 19039414730836168315930369)
  ·
    refine ⟨14279561048127126236947777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19039414730836168315930369 14279561048127126236947777)
    ·
      refine ⟨10709670786095344677710833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14279561048127126236947777 10709670786095344677710833)
      ·
        refine ⟨8032253089571508508283125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10709670786095344677710833 8032253089571508508283125)
        ·
          refine ⟨753023727147328922651543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8032253089571508508283125 753023727147328922651543)
          ·
            refine ⟨1129535590720993383977315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753023727147328922651543 1129535590720993383977315)
            ·
              refine ⟨1694303386081490075965973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129535590720993383977315 1694303386081490075965973)
              ·
                refine ⟨79420471222569847310905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1694303386081490075965973 79420471222569847310905)
                ·
                  rfl

theorem cell21_1044028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 6].length) (baseStart_1044028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1044028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1044028 prefixEnd_1044028 := by exact prefixLift 1044028
  have htrace : WordTrace (prefixWord ++ tailWord_1044028) baseStart_1044028 baseEnd_1044028 := by
    simpa [prefixWord, tailWord_1044028, baseEnd_1044028] using wordTrace_append hprefix tailTrace_1044028
  have hstable : (prefixWord ++ tailWord_1044028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044028).length < 2 ^ (prefixWord ++ tailWord_1044028).sum := by decide
  have hdescent : baseEnd_1044028 < baseStart_1044028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
