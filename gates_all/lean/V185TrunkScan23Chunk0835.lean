import V185TrunkScan23Chunk0834

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4942192 : List Nat := [2, 1, 1, 1, 4, 3, 4, 1, 2, 1, 3]
def baseStart_4942192 : Nat := 118140960795 + 4942192 * 2 ^ 59
def prefixEnd_4942192 : Nat := 4983230072969 + 3 ^ 40 * 4942192 * 2
def baseEnd_4942192 : Nat := 2537719982805432884771279

theorem tailTrace_4942192 : CollatzResearch.WordTrace tailWord_4942192 prefixEnd_4942192 2537719982805432884771279 := by
  unfold tailWord_4942192
  simp only [CollatzResearch.WordTrace]
  refine ⟨90128275455644959019862415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120171033940859945359816553 90128275455644959019862415)
  ·
    refine ⟨135192413183467438529793623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90128275455644959019862415 135192413183467438529793623)
    ·
      refine ⟨202788619775201157794690435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135192413183467438529793623 202788619775201157794690435)
      ·
        refine ⟨304182929662801736692035653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202788619775201157794690435 304182929662801736692035653)
        ·
          refine ⟨57034299311775325629756685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 304182929662801736692035653 57034299311775325629756685)
          ·
            refine ⟨21387862241915747111158757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57034299311775325629756685 21387862241915747111158757)
            ·
              refine ⟨4010224170359202583342267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21387862241915747111158757 4010224170359202583342267)
              ·
                refine ⟨6015336255538803875013401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4010224170359202583342267 6015336255538803875013401)
                ·
                  refine ⟨4511502191654102906260051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6015336255538803875013401 4511502191654102906260051)
                  ·
                    refine ⟨6767253287481154359390077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4511502191654102906260051 6767253287481154359390077)
                    ·
                      refine ⟨2537719982805432884771279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6767253287481154359390077 2537719982805432884771279)
                      ·
                        rfl

theorem cell23_4942192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 2, 1, 3].length) (baseStart_4942192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942192 prefixEnd_4942192 := by exact prefixLift 4942192
  have htrace : WordTrace (prefixWord ++ tailWord_4942192) baseStart_4942192 baseEnd_4942192 := by
    simpa [prefixWord, tailWord_4942192, baseEnd_4942192] using wordTrace_append hprefix tailTrace_4942192
  have hstable : (prefixWord ++ tailWord_4942192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942192).length < 2 ^ (prefixWord ++ tailWord_4942192).sum := by decide
  have hdescent : baseEnd_4942192 < baseStart_4942192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942215 : List Nat := [1, 1, 4, 2, 2, 1, 3, 2, 1, 4, 2]
def baseStart_4942215 : Nat := 118140960795 + 4942215 * 2 ^ 59
def prefixEnd_4942215 : Nat := 4983230072969 + 3 ^ 40 * 4942215 * 2
def baseEnd_4942215 : Nat := 2537731792860486294783673

theorem tailTrace_4942215 : CollatzResearch.WordTrace tailWord_4942215 prefixEnd_4942215 2537731792860486294783673 := by
  unfold tailWord_4942215
  simp only [CollatzResearch.WordTrace]
  refine ⟨180257389790206592967812099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120171593193471061978541399 180257389790206592967812099)
  ·
    refine ⟨270386084685309889451718149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180257389790206592967812099 270386084685309889451718149)
    ·
      refine ⟨50697390878495604272197153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 270386084685309889451718149 50697390878495604272197153)
      ·
        refine ⟨38023043158871703204147865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50697390878495604272197153 38023043158871703204147865)
        ·
          refine ⟨28517282369153777403110899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38023043158871703204147865 28517282369153777403110899)
          ·
            refine ⟨42775923553730666104666349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28517282369153777403110899 42775923553730666104666349)
            ·
              refine ⟨16040971332648999789249881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42775923553730666104666349 16040971332648999789249881)
              ·
                refine ⟨12030728499486749841937411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16040971332648999789249881 12030728499486749841937411)
                ·
                  refine ⟨18046092749230124762906117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12030728499486749841937411 18046092749230124762906117)
                  ·
                    refine ⟨3383642390480648393044897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18046092749230124762906117 3383642390480648393044897)
                    ·
                      refine ⟨2537731792860486294783673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3383642390480648393044897 2537731792860486294783673)
                      ·
                        rfl

theorem cell23_4942215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_4942215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942215 prefixEnd_4942215 := by exact prefixLift 4942215
  have htrace : WordTrace (prefixWord ++ tailWord_4942215) baseStart_4942215 baseEnd_4942215 := by
    simpa [prefixWord, tailWord_4942215, baseEnd_4942215] using wordTrace_append hprefix tailTrace_4942215
  have hstable : (prefixWord ++ tailWord_4942215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942215).length < 2 ^ (prefixWord ++ tailWord_4942215).sum := by decide
  have hdescent : baseEnd_4942215 < baseStart_4942215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942231 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 7]
def baseStart_4942231 : Nat := 118140960795 + 4942231 * 2 ^ 59
def prefixEnd_4942231 : Nat := 4983230072969 + 3 ^ 40 * 4942231 * 2
def baseEnd_4942231 : Nat := 2537740008550958232183599

theorem tailTrace_4942231 : CollatzResearch.WordTrace tailWord_4942231 prefixEnd_4942231 2537740008550958232183599 := by
  unfold tailWord_4942231
  simp only [CollatzResearch.WordTrace]
  refine ⟨180257973358148627700394547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120171982238765751800263031 180257973358148627700394547)
  ·
    refine ⟨270386960037222941550591821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180257973358148627700394547 270386960037222941550591821)
    ·
      refine ⟨101395110013958603081471933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270386960037222941550591821 101395110013958603081471933)
      ·
        refine ⟨38023166255234476155551975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101395110013958603081471933 38023166255234476155551975)
        ·
          refine ⟨57034749382851714233327963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38023166255234476155551975 57034749382851714233327963)
          ·
            refine ⟨85552124074277571349991945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57034749382851714233327963 85552124074277571349991945)
            ·
              refine ⟨64164093055708178512493959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85552124074277571349991945 64164093055708178512493959)
              ·
                refine ⟨96246139583562267768740939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64164093055708178512493959 96246139583562267768740939)
                ·
                  refine ⟨144369209375343401653111409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96246139583562267768740939 144369209375343401653111409)
                  ·
                    refine ⟨108276907031507551239833557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 144369209375343401653111409 108276907031507551239833557)
                    ·
                      refine ⟨2537740008550958232183599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108276907031507551239833557 2537740008550958232183599)
                      ·
                        rfl

theorem cell23_4942231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_4942231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942231 prefixEnd_4942231 := by exact prefixLift 4942231
  have htrace : WordTrace (prefixWord ++ tailWord_4942231) baseStart_4942231 baseEnd_4942231 := by
    simpa [prefixWord, tailWord_4942231, baseEnd_4942231] using wordTrace_append hprefix tailTrace_4942231
  have hstable : (prefixWord ++ tailWord_4942231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942231).length < 2 ^ (prefixWord ++ tailWord_4942231).sum := by decide
  have hdescent : baseEnd_4942231 < baseStart_4942231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942305 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 2, 4, 2]
def baseStart_4942305 : Nat := 118140960795 + 4942305 * 2 ^ 59
def prefixEnd_4942305 : Nat := 4983230072969 + 3 ^ 40 * 4942305 * 2
def baseEnd_4942305 : Nat := 2537778006119390942658259

theorem tailTrace_4942305 : CollatzResearch.WordTrace tailWord_4942305 prefixEnd_4942305 2537778006119390942658259 := by
  unfold tailWord_4942305
  simp only [CollatzResearch.WordTrace]
  refine ⟨180260672359880538338588369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120173781573253692225725579 180260672359880538338588369)
  ·
    refine ⟨135195504269910403753941277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180260672359880538338588369 135195504269910403753941277)
    ·
      refine ⟨50698314101216401407727979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135195504269910403753941277 50698314101216401407727979)
      ·
        refine ⟨76047471151824602111591969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50698314101216401407727979 76047471151824602111591969)
        ·
          refine ⟨57035603363868451583693977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76047471151824602111591969 57035603363868451583693977)
          ·
            refine ⟨42776702522901338687770483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57035603363868451583693977 42776702522901338687770483)
            ·
              refine ⟨64165053784352008031655725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42776702522901338687770483 64165053784352008031655725)
              ·
                refine ⟨24061895169132003011870897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64165053784352008031655725 24061895169132003011870897)
                ·
                  refine ⟨18046421376849002258903173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24061895169132003011870897 18046421376849002258903173)
                  ·
                    refine ⟨3383704008159187923544345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18046421376849002258903173 3383704008159187923544345)
                    ·
                      refine ⟨2537778006119390942658259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3383704008159187923544345 2537778006119390942658259)
                      ·
                        rfl

theorem cell23_4942305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_4942305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942305 prefixEnd_4942305 := by exact prefixLift 4942305
  have htrace : WordTrace (prefixWord ++ tailWord_4942305) baseStart_4942305 baseEnd_4942305 := by
    simpa [prefixWord, tailWord_4942305, baseEnd_4942305] using wordTrace_append hprefix tailTrace_4942305
  have hstable : (prefixWord ++ tailWord_4942305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942305).length < 2 ^ (prefixWord ++ tailWord_4942305).sum := by decide
  have hdescent : baseEnd_4942305 < baseStart_4942305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942389 : List Nat := [1, 3, 3, 1, 1, 2, 2, 5, 1, 1, 3]
def baseStart_4942389 : Nat := 118140960795 + 4942389 * 2 ^ 59
def prefixEnd_4942389 : Nat := 4983230072969 + 3 ^ 40 * 4942389 * 2
def baseEnd_4942389 : Nat := 2537821138494368614007873

theorem tailTrace_4942389 : CollatzResearch.WordTrace tailWord_4942389 prefixEnd_4942389 2537821138494368614007873 := by
  unfold tailWord_4942389
  simp only [CollatzResearch.WordTrace]
  refine ⟨180263736091576220684646221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120175824061050813789764147 180263736091576220684646221)
  ·
    refine ⟨67598901034341082756742333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180263736091576220684646221 67598901034341082756742333)
    ·
      refine ⟨25349587887877906033778375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67598901034341082756742333 25349587887877906033778375)
      ·
        refine ⟨38024381831816859050667563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25349587887877906033778375 38024381831816859050667563)
        ·
          refine ⟨57036572747725288576001345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38024381831816859050667563 57036572747725288576001345)
          ·
            refine ⟨42777429560793966432001009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57036572747725288576001345 42777429560793966432001009)
            ·
              refine ⟨32083072170595474824000757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42777429560793966432001009 32083072170595474824000757)
              ·
                refine ⟨3007788015993325764750071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32083072170595474824000757 3007788015993325764750071)
                ·
                  refine ⟨4511682023989988647125107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3007788015993325764750071 4511682023989988647125107)
                  ·
                    refine ⟨6767523035984982970687661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4511682023989988647125107 6767523035984982970687661)
                    ·
                      refine ⟨2537821138494368614007873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6767523035984982970687661 2537821138494368614007873)
                      ·
                        rfl

theorem cell23_4942389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_4942389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942389 prefixEnd_4942389 := by exact prefixLift 4942389
  have htrace : WordTrace (prefixWord ++ tailWord_4942389) baseStart_4942389 baseEnd_4942389 := by
    simpa [prefixWord, tailWord_4942389, baseEnd_4942389] using wordTrace_append hprefix tailTrace_4942389
  have hstable : (prefixWord ++ tailWord_4942389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942389).length < 2 ^ (prefixWord ++ tailWord_4942389).sum := by decide
  have hdescent : baseEnd_4942389 < baseStart_4942389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942392 : List Nat := [2, 1, 2, 1, 4, 1, 5, 1, 1, 5]
def baseStart_4942392 : Nat := 118140960795 + 4942392 * 2 ^ 59
def prefixEnd_4942392 : Nat := 4983230072969 + 3 ^ 40 * 4942392 * 2
def baseEnd_4942392 : Nat := 845940892978777367423453

theorem tailTrace_4942392 : CollatzResearch.WordTrace tailWord_4942392 prefixEnd_4942392 845940892978777367423453 := by
  unfold tailWord_4942392
  simp only [CollatzResearch.WordTrace]
  refine ⟨90131922755282676098502715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120175897007043568131336953 90131922755282676098502715)
  ·
    refine ⟨135197884132924014147754073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90131922755282676098502715 135197884132924014147754073)
    ·
      refine ⟨101398413099693010610815555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135197884132924014147754073 101398413099693010610815555)
      ·
        refine ⟨152097619649539515916223333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101398413099693010610815555 152097619649539515916223333)
        ·
          refine ⟨28518303684288659234291875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152097619649539515916223333 28518303684288659234291875)
          ·
            refine ⟨42777455526432988851437813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28518303684288659234291875 42777455526432988851437813)
            ·
              refine ⟨4010386455603092704822295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42777455526432988851437813 4010386455603092704822295)
              ·
                refine ⟨6015579683404639057233443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4010386455603092704822295 6015579683404639057233443)
                ·
                  refine ⟨9023369525106958585850165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6015579683404639057233443 9023369525106958585850165)
                  ·
                    refine ⟨845940892978777367423453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9023369525106958585850165 845940892978777367423453)
                    ·
                      rfl

theorem cell23_4942392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 1, 5].length) (baseStart_4942392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942392 prefixEnd_4942392 := by exact prefixLift 4942392
  have htrace : WordTrace (prefixWord ++ tailWord_4942392) baseStart_4942392 baseEnd_4942392 := by
    simpa [prefixWord, tailWord_4942392, baseEnd_4942392] using wordTrace_append hprefix tailTrace_4942392
  have hstable : (prefixWord ++ tailWord_4942392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942392).length < 2 ^ (prefixWord ++ tailWord_4942392).sum := by decide
  have hdescent : baseEnd_4942392 < baseStart_4942392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942408 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_4942408 : Nat := 118140960795 + 4942408 * 2 ^ 59
def prefixEnd_4942408 : Nat := 4983230072969 + 3 ^ 40 * 4942408 * 2
def baseEnd_4942408 : Nat := 2537830894626804039670285

theorem tailTrace_4942408 : CollatzResearch.WordTrace tailWord_4942408 prefixEnd_4942408 2537830894626804039670285 := by
  unfold tailWord_4942408
  simp only [CollatzResearch.WordTrace]
  refine ⟨90132214539253693464793939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120176286052338257953058585 90132214539253693464793939)
  ·
    refine ⟨135198321808880540197190909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90132214539253693464793939 135198321808880540197190909)
    ·
      refine ⟨50699370678330202573946591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135198321808880540197190909 50699370678330202573946591)
      ·
        refine ⟨76049056017495303860919887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50699370678330202573946591 76049056017495303860919887)
        ·
          refine ⟨114073584026242955791379831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76049056017495303860919887 114073584026242955791379831)
          ·
            refine ⟨171110376039364433687069747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114073584026242955791379831 171110376039364433687069747)
            ·
              refine ⟨256665564059046650530604621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171110376039364433687069747 256665564059046650530604621)
              ·
                refine ⟨96249586522142493948976733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 256665564059046650530604621 96249586522142493948976733)
                ·
                  refine ⟨36093594945803435230866275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96249586522142493948976733 36093594945803435230866275)
                  ·
                    refine ⟨54140392418705152846299413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36093594945803435230866275 54140392418705152846299413)
                    ·
                      refine ⟨2537830894626804039670285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54140392418705152846299413 2537830894626804039670285)
                      ·
                        rfl

theorem cell23_4942408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_4942408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942408 prefixEnd_4942408 := by exact prefixLift 4942408
  have htrace : WordTrace (prefixWord ++ tailWord_4942408) baseStart_4942408 baseEnd_4942408 := by
    simpa [prefixWord, tailWord_4942408, baseEnd_4942408] using wordTrace_append hprefix tailTrace_4942408
  have hstable : (prefixWord ++ tailWord_4942408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942408).length < 2 ^ (prefixWord ++ tailWord_4942408).sum := by decide
  have hdescent : baseEnd_4942408 < baseStart_4942408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942415 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 3]
def baseStart_4942415 : Nat := 118140960795 + 4942415 * 2 ^ 59
def prefixEnd_4942415 : Nat := 4983230072969 + 3 ^ 40 * 4942415 * 2
def baseEnd_4942415 : Nat := 2537834488991385512282753

theorem tailTrace_4942415 : CollatzResearch.WordTrace tailWord_4942415 prefixEnd_4942415 2537834488991385512282753 := by
  unfold tailWord_4942415
  simp only [CollatzResearch.WordTrace]
  refine ⟨180264684389482027125092699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120176456259654684750061799 180264684389482027125092699)
  ·
    refine ⟨270397026584223040687639049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180264684389482027125092699 270397026584223040687639049)
    ·
      refine ⟨202797769938167280515729287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270397026584223040687639049 202797769938167280515729287)
      ·
        refine ⟨304196654907250920773593931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202797769938167280515729287 304196654907250920773593931)
        ·
          refine ⟨456294982360876381160390897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304196654907250920773593931 456294982360876381160390897)
          ·
            refine ⟨342221236770657285870293173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 456294982360876381160390897 342221236770657285870293173)
            ·
              refine ⟨32083240947249120550339985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 342221236770657285870293173 32083240947249120550339985)
              ·
                refine ⟨24062430710436840412754989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32083240947249120550339985 24062430710436840412754989)
                ·
                  refine ⟨9023411516413815154783121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24062430710436840412754989 9023411516413815154783121)
                  ·
                    refine ⟨6767558637310361366087341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9023411516413815154783121 6767558637310361366087341)
                    ·
                      refine ⟨2537834488991385512282753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6767558637310361366087341 2537834488991385512282753)
                      ·
                        rfl

theorem cell23_4942415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 3].length) (baseStart_4942415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942415 prefixEnd_4942415 := by exact prefixLift 4942415
  have htrace : WordTrace (prefixWord ++ tailWord_4942415) baseStart_4942415 baseEnd_4942415 := by
    simpa [prefixWord, tailWord_4942415, baseEnd_4942415] using wordTrace_append hprefix tailTrace_4942415
  have hstable : (prefixWord ++ tailWord_4942415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942415).length < 2 ^ (prefixWord ++ tailWord_4942415).sum := by decide
  have hdescent : baseEnd_4942415 < baseStart_4942415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942435 : List Nat := [1, 1, 1, 5, 1, 2, 5, 7]
def baseStart_4942435 : Nat := 118140960795 + 4942435 * 2 ^ 59
def prefixEnd_4942435 : Nat := 4983230072969 + 3 ^ 40 * 4942435 * 2
def baseEnd_4942435 : Nat := 93994250318684275334543

theorem tailTrace_4942435 : CollatzResearch.WordTrace tailWord_4942435 prefixEnd_4942435 93994250318684275334543 := by
  unfold tailWord_4942435
  simp only [CollatzResearch.WordTrace]
  refine ⟨180265413849409570540820759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120176942566273047027213839 180265413849409570540820759)
  ·
    refine ⟨270398120774114355811231139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180265413849409570540820759 270398120774114355811231139)
    ·
      refine ⟨405597181161171533716846709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270398120774114355811231139 405597181161171533716846709)
      ·
        refine ⟨38024735733859831285954379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 405597181161171533716846709 38024735733859831285954379)
        ·
          refine ⟨57037103600789746928931569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38024735733859831285954379 57037103600789746928931569)
          ·
            refine ⟨42777827700592310196698677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57037103600789746928931569 42777827700592310196698677)
            ·
              refine ⟨4010421346930529080940501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42777827700592310196698677 4010421346930529080940501)
              ·
                refine ⟨93994250318684275334543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4010421346930529080940501 93994250318684275334543)
                ·
                  rfl

theorem cell23_4942435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 7].length) (baseStart_4942435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942435 prefixEnd_4942435 := by exact prefixLift 4942435
  have htrace : WordTrace (prefixWord ++ tailWord_4942435) baseStart_4942435 baseEnd_4942435 := by
    simpa [prefixWord, tailWord_4942435, baseEnd_4942435] using wordTrace_append hprefix tailTrace_4942435
  have hstable : (prefixWord ++ tailWord_4942435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942435).length < 2 ^ (prefixWord ++ tailWord_4942435).sum := by decide
  have hdescent : baseEnd_4942435 < baseStart_4942435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942446 : List Nat := [4, 1, 2, 2, 2, 3, 2, 1, 1, 1, 4]
def baseStart_4942446 : Nat := 118140960795 + 4942446 * 2 ^ 59
def prefixEnd_4942446 : Nat := 4983230072969 + 3 ^ 40 * 4942446 * 2
def baseEnd_4942446 : Nat := 2537850406891674890995111

theorem tailTrace_4942446 : CollatzResearch.WordTrace tailWord_4942446 prefixEnd_4942446 2537850406891674890995111 := by
  unfold tailWord_4942446
  simp only [CollatzResearch.WordTrace]
  refine ⟨22533226881546214927433899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120177210034913146279647461 22533226881546214927433899)
  ·
    refine ⟨33799840322319322391150849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22533226881546214927433899 33799840322319322391150849)
    ·
      refine ⟨25349880241739491793363137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33799840322319322391150849 25349880241739491793363137)
      ·
        refine ⟨19012410181304618845022353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25349880241739491793363137 19012410181304618845022353)
        ·
          refine ⟨14259307635978464133766765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19012410181304618845022353 14259307635978464133766765)
          ·
            refine ⟨5347240363491924050162537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14259307635978464133766765 5347240363491924050162537)
            ·
              refine ⟨4010430272618943037621903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5347240363491924050162537 4010430272618943037621903)
              ·
                refine ⟨6015645408928414556432855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4010430272618943037621903 6015645408928414556432855)
                ·
                  refine ⟨9023468113392621834649283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6015645408928414556432855 9023468113392621834649283)
                  ·
                    refine ⟨13535202170088932751973925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9023468113392621834649283 13535202170088932751973925)
                    ·
                      refine ⟨2537850406891674890995111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13535202170088932751973925 2537850406891674890995111)
                      ·
                        rfl

theorem cell23_4942446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_4942446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942446 prefixEnd_4942446 := by exact prefixLift 4942446
  have htrace : WordTrace (prefixWord ++ tailWord_4942446) baseStart_4942446 baseEnd_4942446 := by
    simpa [prefixWord, tailWord_4942446, baseEnd_4942446] using wordTrace_append hprefix tailTrace_4942446
  have hstable : (prefixWord ++ tailWord_4942446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942446).length < 2 ^ (prefixWord ++ tailWord_4942446).sum := by decide
  have hdescent : baseEnd_4942446 < baseStart_4942446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942489 : List Nat := [1, 2, 1, 2, 1, 2, 6, 2, 1, 3, 2]
def baseStart_4942489 : Nat := 118140960795 + 4942489 * 2 ^ 59
def prefixEnd_4942489 : Nat := 4983230072969 + 3 ^ 40 * 4942489 * 2
def baseEnd_4942489 : Nat := 2537872486559818222757413

theorem tailTrace_4942489 : CollatzResearch.WordTrace tailWord_4942489 prefixEnd_4942489 2537872486559818222757413 := by
  unfold tailWord_4942489
  simp only [CollatzResearch.WordTrace]
  refine ⟨180267383391213937763286521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120178255594142625175524347 180267383391213937763286521)
  ·
    refine ⟨135200537543410453322464891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180267383391213937763286521 135200537543410453322464891)
    ·
      refine ⟨202800806315115679983697337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135200537543410453322464891 202800806315115679983697337)
      ·
        refine ⟨152100604736336759987773003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202800806315115679983697337 152100604736336759987773003)
        ·
          refine ⟨228150907104505139981659505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152100604736336759987773003 228150907104505139981659505)
          ·
            refine ⟨171113180328378854986244629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228150907104505139981659505 171113180328378854986244629)
            ·
              refine ⟨8020930327892758827480217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 171113180328378854986244629 8020930327892758827480217)
              ·
                refine ⟨6015697745919569120610163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8020930327892758827480217 6015697745919569120610163)
                ·
                  refine ⟨9023546618879353680915245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6015697745919569120610163 9023546618879353680915245)
                  ·
                    refine ⟨3383829982079757630343217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9023546618879353680915245 3383829982079757630343217)
                    ·
                      refine ⟨2537872486559818222757413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3383829982079757630343217 2537872486559818222757413)
                      ·
                        rfl

theorem cell23_4942489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 3, 2].length) (baseStart_4942489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942489 prefixEnd_4942489 := by exact prefixLift 4942489
  have htrace : WordTrace (prefixWord ++ tailWord_4942489) baseStart_4942489 baseEnd_4942489 := by
    simpa [prefixWord, tailWord_4942489, baseEnd_4942489] using wordTrace_append hprefix tailTrace_4942489
  have hstable : (prefixWord ++ tailWord_4942489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942489).length < 2 ^ (prefixWord ++ tailWord_4942489).sum := by decide
  have hdescent : baseEnd_4942489 < baseStart_4942489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942536 : List Nat := [2, 1, 3, 1, 2, 4, 1, 3, 2, 2, 2]
def baseStart_4942536 : Nat := 118140960795 + 4942536 * 2 ^ 59
def prefixEnd_4942536 : Nat := 4983230072969 + 3 ^ 40 * 4942536 * 2
def baseEnd_4942536 : Nat := 2537896620150579538869697

theorem tailTrace_4942536 : CollatzResearch.WordTrace tailWord_4942536 prefixEnd_4942536 2537896620150579538869697 := by
  unfold tailWord_4942536
  simp only [CollatzResearch.WordTrace]
  refine ⟨90134548811021832395123731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120179398414695776526831641 90134548811021832395123731)
  ·
    refine ⟨135201823216532748592685597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90134548811021832395123731 135201823216532748592685597)
    ·
      refine ⟨50700683706199780722257099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135201823216532748592685597 50700683706199780722257099)
      ·
        refine ⟨76051025559299671083385649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50700683706199780722257099 76051025559299671083385649)
        ·
          refine ⟨57038269169474753312539237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76051025559299671083385649 57038269169474753312539237)
          ·
            refine ⟨10694675469276516246101107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57038269169474753312539237 10694675469276516246101107)
            ·
              refine ⟨16042013203914774369151661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10694675469276516246101107 16042013203914774369151661)
              ·
                refine ⟨6015754951468040388431873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16042013203914774369151661 6015754951468040388431873)
                ·
                  refine ⟨4511816213601030291323905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6015754951468040388431873 4511816213601030291323905)
                  ·
                    refine ⟨3383862160200772718492929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4511816213601030291323905 3383862160200772718492929)
                    ·
                      refine ⟨2537896620150579538869697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3383862160200772718492929 2537896620150579538869697)
                      ·
                        rfl

theorem cell23_4942536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_4942536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942536 prefixEnd_4942536 := by exact prefixLift 4942536
  have htrace : WordTrace (prefixWord ++ tailWord_4942536) baseStart_4942536 baseEnd_4942536 := by
    simpa [prefixWord, tailWord_4942536, baseEnd_4942536] using wordTrace_append hprefix tailTrace_4942536
  have hstable : (prefixWord ++ tailWord_4942536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942536).length < 2 ^ (prefixWord ++ tailWord_4942536).sum := by decide
  have hdescent : baseEnd_4942536 < baseStart_4942536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942582 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_4942582 : Nat := 118140960795 + 4942582 * 2 ^ 59
def prefixEnd_4942582 : Nat := 4983230072969 + 3 ^ 40 * 4942582 * 2
def baseEnd_4942582 : Nat := 2537920240260686358894485

theorem tailTrace_4942582 : CollatzResearch.WordTrace tailWord_4942582 prefixEnd_4942582 2537920240260686358894485 := by
  unfold tailWord_4942582
  simp only [CollatzResearch.WordTrace]
  refine ⟨11266923461242313415401375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120180516919918009764281333 11266923461242313415401375)
  ·
    refine ⟨16900385191863470123102063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11266923461242313415401375 16900385191863470123102063)
    ·
      refine ⟨25350577787795205184653095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16900385191863470123102063 25350577787795205184653095)
      ·
        refine ⟨38025866681692807776979643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25350577787795205184653095 38025866681692807776979643)
        ·
          refine ⟨57038800022539211665469465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38025866681692807776979643 57038800022539211665469465)
          ·
            refine ⟨42779100016904408749102099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57038800022539211665469465 42779100016904408749102099)
            ·
              refine ⟨64168650025356613123653149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42779100016904408749102099 64168650025356613123653149)
              ·
                refine ⟨24063243759508729921369931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64168650025356613123653149 24063243759508729921369931)
                ·
                  refine ⟨36094865639263094882054897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24063243759508729921369931 36094865639263094882054897)
                  ·
                    refine ⟨27071149229447321161541173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36094865639263094882054897 27071149229447321161541173)
                    ·
                      refine ⟨2537920240260686358894485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27071149229447321161541173 2537920240260686358894485)
                      ·
                        rfl

theorem cell23_4942582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_4942582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942582 prefixEnd_4942582 := by exact prefixLift 4942582
  have htrace : WordTrace (prefixWord ++ tailWord_4942582) baseStart_4942582 baseEnd_4942582 := by
    simpa [prefixWord, tailWord_4942582, baseEnd_4942582] using wordTrace_append hprefix tailTrace_4942582
  have hstable : (prefixWord ++ tailWord_4942582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942582).length < 2 ^ (prefixWord ++ tailWord_4942582).sum := by decide
  have hdescent : baseEnd_4942582 < baseStart_4942582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942632 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 8]
def baseStart_4942632 : Nat := 118140960795 + 4942632 * 2 ^ 59
def prefixEnd_4942632 : Nat := 4983230072969 + 3 ^ 40 * 4942632 * 2
def baseEnd_4942632 : Nat := 281993990477045684807695

theorem tailTrace_4942632 : CollatzResearch.WordTrace tailWord_4942632 prefixEnd_4942632 281993990477045684807695 := by
  unfold tailWord_4942632
  simp only [CollatzResearch.WordTrace]
  refine ⟨90136299514847936592871075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120181732686463915457161433 90136299514847936592871075)
  ·
    refine ⟨135204449272271904889306613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90136299514847936592871075 135204449272271904889306613)
    ·
      refine ⟨12675417119275491083372495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135204449272271904889306613 12675417119275491083372495)
      ·
        refine ⟨19013125678913236625058743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12675417119275491083372495 19013125678913236625058743)
        ·
          refine ⟨28519688518369854937588115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19013125678913236625058743 28519688518369854937588115)
          ·
            refine ⟨42779532777554782406382173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28519688518369854937588115 42779532777554782406382173)
            ·
              refine ⟨16042324791583043402393315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42779532777554782406382173 16042324791583043402393315)
              ·
                refine ⟨24063487187374565103589973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16042324791583043402393315 24063487187374565103589973)
                ·
                  refine ⟨281993990477045684807695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24063487187374565103589973 281993990477045684807695)
                  ·
                    rfl

theorem cell23_4942632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 8].length) (baseStart_4942632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942632 prefixEnd_4942632 := by exact prefixLift 4942632
  have htrace : WordTrace (prefixWord ++ tailWord_4942632) baseStart_4942632 baseEnd_4942632 := by
    simpa [prefixWord, tailWord_4942632, baseEnd_4942632] using wordTrace_append hprefix tailTrace_4942632
  have hstable : (prefixWord ++ tailWord_4942632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942632).length < 2 ^ (prefixWord ++ tailWord_4942632).sum := by decide
  have hdescent : baseEnd_4942632 < baseStart_4942632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942635 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 6]
def baseStart_4942635 : Nat := 118140960795 + 4942635 * 2 ^ 59
def prefixEnd_4942635 : Nat := 4983230072969 + 3 ^ 40 * 4942635 * 2
def baseEnd_4942635 : Nat := 2537947454735374651531741

theorem tailTrace_4942635 : CollatzResearch.WordTrace tailWord_4942635 prefixEnd_4942635 2537947454735374651531741 := by
  unfold tailWord_4942635
  simp only [CollatzResearch.WordTrace]
  refine ⟨180272708448685004698101359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120181805632456669798734239 180272708448685004698101359)
  ·
    refine ⟨270409062673027507047152039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180272708448685004698101359 270409062673027507047152039)
    ·
      refine ⟨405613594009541260570728059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270409062673027507047152039 405613594009541260570728059)
      ·
        refine ⟨608420391014311890856092089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405613594009541260570728059 608420391014311890856092089)
        ·
          refine ⟨456315293260733918142069067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 608420391014311890856092089 456315293260733918142069067)
          ·
            refine ⟨684472939891100877213103601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456315293260733918142069067 684472939891100877213103601)
            ·
              refine ⟨513354704918325657909827701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 684472939891100877213103601 513354704918325657909827701)
              ·
                refine ⟨48127003586093030429046347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 513354704918325657909827701 48127003586093030429046347)
                ·
                  refine ⟨72190505379139545643569521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48127003586093030429046347 72190505379139545643569521)
                  ·
                    refine ⟨54142879034354659232677141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72190505379139545643569521 54142879034354659232677141)
                    ·
                      refine ⟨2537947454735374651531741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54142879034354659232677141 2537947454735374651531741)
                      ·
                        rfl

theorem cell23_4942635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 6].length) (baseStart_4942635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942635 prefixEnd_4942635 := by exact prefixLift 4942635
  have htrace : WordTrace (prefixWord ++ tailWord_4942635) baseStart_4942635 baseEnd_4942635 := by
    simpa [prefixWord, tailWord_4942635, baseEnd_4942635] using wordTrace_append hprefix tailTrace_4942635
  have hstable : (prefixWord ++ tailWord_4942635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942635).length < 2 ^ (prefixWord ++ tailWord_4942635).sum := by decide
  have hdescent : baseEnd_4942635 < baseStart_4942635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942659 : List Nat := [1, 1, 1, 3, 1, 4, 1, 4, 3, 1, 3]
def baseStart_4942659 : Nat := 118140960795 + 4942659 * 2 ^ 59
def prefixEnd_4942659 : Nat := 4983230072969 + 3 ^ 40 * 4942659 * 2
def baseEnd_4942659 : Nat := 2537959778271082557631631

theorem tailTrace_4942659 : CollatzResearch.WordTrace tailWord_4942659 prefixEnd_4942659 2537959778271082557631631 := by
  unfold tailWord_4942659
  simp only [CollatzResearch.WordTrace]
  refine ⟨180273583800598056796975031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120182389200398704531316687 180273583800598056796975031)
  ·
    refine ⟨270410375700897085195462547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180273583800598056796975031 270410375700897085195462547)
    ·
      refine ⟨405615563551345627793193821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270410375700897085195462547 405615563551345627793193821)
      ·
        refine ⟨152105836331754610422447683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 405615563551345627793193821 152105836331754610422447683)
        ·
          refine ⟨228158754497631915633671525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152105836331754610422447683 228158754497631915633671525)
          ·
            refine ⟨42779766468305984181313411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228158754497631915633671525 42779766468305984181313411)
            ·
              refine ⟨64169649702458976271970117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42779766468305984181313411 64169649702458976271970117)
              ·
                refine ⟨12031809319211058050994397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64169649702458976271970117 12031809319211058050994397)
                ·
                  refine ⟨4511928494704146769122899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12031809319211058050994397 4511928494704146769122899)
                  ·
                    refine ⟨6767892742056220153684349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4511928494704146769122899 6767892742056220153684349)
                    ·
                      refine ⟨2537959778271082557631631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6767892742056220153684349 2537959778271082557631631)
                      ·
                        rfl

theorem cell23_4942659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 1, 3].length) (baseStart_4942659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942659 prefixEnd_4942659 := by exact prefixLift 4942659
  have htrace : WordTrace (prefixWord ++ tailWord_4942659) baseStart_4942659 baseEnd_4942659 := by
    simpa [prefixWord, tailWord_4942659, baseEnd_4942659] using wordTrace_append hprefix tailTrace_4942659
  have hstable : (prefixWord ++ tailWord_4942659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942659).length < 2 ^ (prefixWord ++ tailWord_4942659).sum := by decide
  have hdescent : baseEnd_4942659 < baseStart_4942659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942679 : List Nat := [1, 1, 3, 2, 4, 1, 2, 3, 1, 5]
def baseStart_4942679 : Nat := 118140960795 + 4942679 * 2 ^ 59
def prefixEnd_4942679 : Nat := 4983230072969 + 3 ^ 40 * 4942679 * 2
def baseEnd_4942679 : Nat := 845990015961390826460513

theorem tailTrace_4942679 : CollatzResearch.WordTrace tailWord_4942679 prefixEnd_4942679 845990015961390826460513 := by
  unfold tailWord_4942679
  simp only [CollatzResearch.WordTrace]
  refine ⟨180274313260525600212703091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120182875507017066808468727 180274313260525600212703091)
  ·
    refine ⟨270411469890788400319054637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180274313260525600212703091 270411469890788400319054637)
    ·
      refine ⟨101404301209045650119645489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270411469890788400319054637 101404301209045650119645489)
      ·
        refine ⟨76053225906784237589734117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101404301209045650119645489 76053225906784237589734117)
        ·
          refine ⟨14259979857522044548075147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76053225906784237589734117 14259979857522044548075147)
          ·
            refine ⟨21389969786283066822112721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14259979857522044548075147 21389969786283066822112721)
            ·
              refine ⟨16042477339712300116584541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21389969786283066822112721 16042477339712300116584541)
              ·
                refine ⟨6015929002392112543719203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16042477339712300116584541 6015929002392112543719203)
                ·
                  refine ⟨9023893503588168815578805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6015929002392112543719203 9023893503588168815578805)
                  ·
                    refine ⟨845990015961390826460513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9023893503588168815578805 845990015961390826460513)
                    ·
                      rfl

theorem cell23_4942679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 5].length) (baseStart_4942679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942679 prefixEnd_4942679 := by exact prefixLift 4942679
  have htrace : WordTrace (prefixWord ++ tailWord_4942679) baseStart_4942679 baseEnd_4942679 := by
    simpa [prefixWord, tailWord_4942679, baseEnd_4942679] using wordTrace_append hprefix tailTrace_4942679
  have hstable : (prefixWord ++ tailWord_4942679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942679).length < 2 ^ (prefixWord ++ tailWord_4942679).sum := by decide
  have hdescent : baseEnd_4942679 < baseStart_4942679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942716 : List Nat := [2, 2, 2, 1, 1, 1, 1, 6, 3, 2, 2]
def baseStart_4942716 : Nat := 118140960795 + 4942716 * 2 ^ 59
def prefixEnd_4942716 : Nat := 4983230072969 + 3 ^ 40 * 4942716 * 2
def baseEnd_4942716 : Nat := 2537989046668388834618869

theorem tailTrace_4942716 : CollatzResearch.WordTrace tailWord_4942716 prefixEnd_4942716 2537989046668388834618869 := by
  unfold tailWord_4942716
  simp only [CollatzResearch.WordTrace]
  refine ⟨90137831380695777765900001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120183775174261037021200001 90137831380695777765900001)
  ·
    refine ⟨67603373535521833324425001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90137831380695777765900001 67603373535521833324425001)
    ·
      refine ⟨50702530151641374993318751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67603373535521833324425001 50702530151641374993318751)
      ·
        refine ⟨76053795227462062489978127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50702530151641374993318751 76053795227462062489978127)
        ·
          refine ⟨114080692841193093734967191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76053795227462062489978127 114080692841193093734967191)
          ·
            refine ⟨171121039261789640602450787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114080692841193093734967191 171121039261789640602450787)
            ·
              refine ⟨256681558892684460903676181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171121039261789640602450787 256681558892684460903676181)
              ·
                refine ⟨12031948073094584104859821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 256681558892684460903676181 12031948073094584104859821)
                ·
                  refine ⟨4511980527410469039322433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12031948073094584104859821 4511980527410469039322433)
                  ·
                    refine ⟨3383985395557851779491825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4511980527410469039322433 3383985395557851779491825)
                    ·
                      refine ⟨2537989046668388834618869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3383985395557851779491825 2537989046668388834618869)
                      ·
                        rfl

theorem cell23_4942716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_4942716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942716 prefixEnd_4942716 := by exact prefixLift 4942716
  have htrace : WordTrace (prefixWord ++ tailWord_4942716) baseStart_4942716 baseEnd_4942716 := by
    simpa [prefixWord, tailWord_4942716, baseEnd_4942716] using wordTrace_append hprefix tailTrace_4942716
  have hstable : (prefixWord ++ tailWord_4942716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942716).length < 2 ^ (prefixWord ++ tailWord_4942716).sum := by decide
  have hdescent : baseEnd_4942716 < baseStart_4942716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942729 : List Nat := [1, 2, 1, 1, 5, 3, 1, 2, 1, 2, 4]
def baseStart_4942729 : Nat := 118140960795 + 4942729 * 2 ^ 59
def prefixEnd_4942729 : Nat := 4983230072969 + 3 ^ 40 * 4942729 * 2
def baseEnd_4942729 : Nat := 2537995721916897283756309

theorem tailTrace_4942729 : CollatzResearch.WordTrace tailWord_4942729 prefixEnd_4942729 2537995721916897283756309 := by
  unfold tailWord_4942729
  simp only [CollatzResearch.WordTrace]
  refine ⟨180276136910344458752023241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120184091273562972501348827 180276136910344458752023241)
  ·
    refine ⟨135207102682758344064017431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180276136910344458752023241 135207102682758344064017431)
    ·
      refine ⟨202810654024137516096026147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135207102682758344064017431 202810654024137516096026147)
      ·
        refine ⟨304215981036206274144039221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202810654024137516096026147 304215981036206274144039221)
        ·
          refine ⟨28520248222144338201003677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 304215981036206274144039221 28520248222144338201003677)
          ·
            refine ⟨10695093083304126825376379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28520248222144338201003677 10695093083304126825376379)
            ·
              refine ⟨16042639624956190238064569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10695093083304126825376379 16042639624956190238064569)
              ·
                refine ⟨12031979718717142678548427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16042639624956190238064569 12031979718717142678548427)
                ·
                  refine ⟨18047969578075714017822641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12031979718717142678548427 18047969578075714017822641)
                  ·
                    refine ⟨13535977183556785513366981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18047969578075714017822641 13535977183556785513366981)
                    ·
                      refine ⟨2537995721916897283756309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13535977183556785513366981 2537995721916897283756309)
                      ·
                        rfl

theorem cell23_4942729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 2, 4].length) (baseStart_4942729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942729 prefixEnd_4942729 := by exact prefixLift 4942729
  have htrace : WordTrace (prefixWord ++ tailWord_4942729) baseStart_4942729 baseEnd_4942729 := by
    simpa [prefixWord, tailWord_4942729, baseEnd_4942729] using wordTrace_append hprefix tailTrace_4942729
  have hstable : (prefixWord ++ tailWord_4942729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942729).length < 2 ^ (prefixWord ++ tailWord_4942729).sum := by decide
  have hdescent : baseEnd_4942729 < baseStart_4942729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942749 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_4942749 : Nat := 118140960795 + 4942749 * 2 ^ 59
def prefixEnd_4942749 : Nat := 4983230072969 + 3 ^ 40 * 4942749 * 2
def baseEnd_4942749 : Nat := 2538005991529987205506217

theorem tailTrace_4942749 : CollatzResearch.WordTrace tailWord_4942749 prefixEnd_4942749 2538005991529987205506217 := by
  unfold tailWord_4942749
  simp only [CollatzResearch.WordTrace]
  refine ⟨180276866370272002167751301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120184577580181334778500867 180276866370272002167751301)
  ·
    refine ⟨33801912444426000406453369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180276866370272002167751301 33801912444426000406453369)
    ·
      refine ⟨25351434333319500304840027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33801912444426000406453369 25351434333319500304840027)
      ·
        refine ⟨38027151499979250457260041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25351434333319500304840027 38027151499979250457260041)
        ·
          refine ⟨28520363624984437842945031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38027151499979250457260041 28520363624984437842945031)
          ·
            refine ⟨42780545437476656764417547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28520363624984437842945031 42780545437476656764417547)
            ·
              refine ⟨64170818156214985146626321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42780545437476656764417547 64170818156214985146626321)
              ·
                refine ⟨48128113617161238859969741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64170818156214985146626321 48128113617161238859969741)
                ·
                  refine ⟨18048042606435464572488653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48128113617161238859969741 18048042606435464572488653)
                  ·
                    refine ⟨6768015977413299214683245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18048042606435464572488653 6768015977413299214683245)
                    ·
                      refine ⟨2538005991529987205506217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6768015977413299214683245 2538005991529987205506217)
                      ·
                        rfl

theorem cell23_4942749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_4942749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942749 prefixEnd_4942749 := by exact prefixLift 4942749
  have htrace : WordTrace (prefixWord ++ tailWord_4942749) baseStart_4942749 baseEnd_4942749 := by
    simpa [prefixWord, tailWord_4942749, baseEnd_4942749] using wordTrace_append hprefix tailTrace_4942749
  have hstable : (prefixWord ++ tailWord_4942749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942749).length < 2 ^ (prefixWord ++ tailWord_4942749).sum := by decide
  have hdescent : baseEnd_4942749 < baseStart_4942749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942752 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 2, 7]
def baseStart_4942752 : Nat := 118140960795 + 4942752 * 2 ^ 59
def prefixEnd_4942752 : Nat := 4983230072969 + 3 ^ 40 * 4942752 * 2
def baseEnd_4942752 : Nat := 846002510657316897922901

theorem tailTrace_4942752 : CollatzResearch.WordTrace tailWord_4942752 prefixEnd_4942752 846002510657316897922901 := by
  unfold tailWord_4942752
  simp only [CollatzResearch.WordTrace]
  refine ⟨90138487894630566840055255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120184650526174089120073673 90138487894630566840055255)
  ·
    refine ⟨135207731841945850260082883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90138487894630566840055255 135207731841945850260082883)
    ·
      refine ⟨202811597762918775390124325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135207731841945850260082883 202811597762918775390124325)
      ·
        refine ⟨38027174580547270385648311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 202811597762918775390124325 38027174580547270385648311)
        ·
          refine ⟨57040761870820905578472467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38027174580547270385648311 57040761870820905578472467)
          ·
            refine ⟨85561142806231358367708701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57040761870820905578472467 85561142806231358367708701)
            ·
              refine ⟨32085428552336759387890763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85561142806231358367708701 32085428552336759387890763)
              ·
                refine ⟨48128142828505139081836145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32085428552336759387890763 48128142828505139081836145)
                ·
                  refine ⟨36096107121378854311377109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48128142828505139081836145 36096107121378854311377109)
                  ·
                    refine ⟨846002510657316897922901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36096107121378854311377109 846002510657316897922901)
                    ·
                      rfl

theorem cell23_4942752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 2, 7].length) (baseStart_4942752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942752 prefixEnd_4942752 := by exact prefixLift 4942752
  have htrace : WordTrace (prefixWord ++ tailWord_4942752) baseStart_4942752 baseEnd_4942752 := by
    simpa [prefixWord, tailWord_4942752, baseEnd_4942752] using wordTrace_append hprefix tailTrace_4942752
  have hstable : (prefixWord ++ tailWord_4942752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942752).length < 2 ^ (prefixWord ++ tailWord_4942752).sum := by decide
  have hdescent : baseEnd_4942752 < baseStart_4942752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942776 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 3, 3, 2]
def baseStart_4942776 : Nat := 118140960795 + 4942776 * 2 ^ 59
def prefixEnd_4942776 : Nat := 4983230072969 + 3 ^ 40 * 4942776 * 2
def baseEnd_4942776 : Nat := 2538019855507658599868593

theorem tailTrace_4942776 : CollatzResearch.WordTrace tailWord_4942776 prefixEnd_4942776 2538019855507658599868593 := by
  unfold tailWord_4942776
  simp only [CollatzResearch.WordTrace]
  refine ⟨90138925570587092889492091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120185234094116123852656121 90138925570587092889492091)
  ·
    refine ⟨135208388355880639334238137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90138925570587092889492091 135208388355880639334238137)
    ·
      refine ⟨101406291266910479500678603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135208388355880639334238137 101406291266910479500678603)
      ·
        refine ⟨152109436900365719251017905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101406291266910479500678603 152109436900365719251017905)
        ·
          refine ⟨114082077675274289438263429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152109436900365719251017905 114082077675274289438263429)
          ·
            refine ⟨21390389564113929269674393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114082077675274289438263429 21390389564113929269674393)
            ·
              refine ⟨16042792173085446952255795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21390389564113929269674393 16042792173085446952255795)
              ·
                refine ⟨24064188259628170428383693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16042792173085446952255795 24064188259628170428383693)
                ·
                  refine ⟨9024070597360563910643885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24064188259628170428383693 9024070597360563910643885)
                  ·
                    refine ⟨3384026474010211466491457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9024070597360563910643885 3384026474010211466491457)
                    ·
                      refine ⟨2538019855507658599868593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3384026474010211466491457 2538019855507658599868593)
                      ·
                        rfl

theorem cell23_4942776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 3, 3, 2].length) (baseStart_4942776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942776 prefixEnd_4942776 := by exact prefixLift 4942776
  have htrace : WordTrace (prefixWord ++ tailWord_4942776) baseStart_4942776 baseEnd_4942776 := by
    simpa [prefixWord, tailWord_4942776, baseEnd_4942776] using wordTrace_append hprefix tailTrace_4942776
  have hstable : (prefixWord ++ tailWord_4942776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942776).length < 2 ^ (prefixWord ++ tailWord_4942776).sum := by decide
  have hdescent : baseEnd_4942776 < baseStart_4942776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942789 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 2, 8, 2]
def baseStart_4942789 : Nat := 118140960795 + 4942789 * 2 ^ 59
def prefixEnd_4942789 : Nat := 4983230072969 + 3 ^ 40 * 4942789 * 2
def baseEnd_4942789 : Nat := 2538026530756167049006033

theorem tailTrace_4942789 : CollatzResearch.WordTrace tailWord_4942789 prefixEnd_4942789 2538026530756167049006033 := by
  unfold tailWord_4942789
  simp only [CollatzResearch.WordTrace]
  refine ⟨180278325290127088999207421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120185550193418059332804947 180278325290127088999207421)
  ·
    refine ⟨67604371983797658374702783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180278325290127088999207421 67604371983797658374702783)
    ·
      refine ⟨101406557975696487562054175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67604371983797658374702783 101406557975696487562054175)
      ·
        refine ⟨152109836963544731343081263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101406557975696487562054175 152109836963544731343081263)
        ·
          refine ⟨228164755445317097014621895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152109836963544731343081263 228164755445317097014621895)
          ·
            refine ⟨342247133167975645521932843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228164755445317097014621895 342247133167975645521932843)
            ·
              refine ⟨513370699751963468282899265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342247133167975645521932843 513370699751963468282899265)
              ·
                refine ⟨385028024813972601212174449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513370699751963468282899265 385028024813972601212174449)
                ·
                  refine ⟨288771018610479450909130837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385028024813972601212174449 288771018610479450909130837)
                  ·
                    refine ⟨3384035374341556065341377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 288771018610479450909130837 3384035374341556065341377)
                    ·
                      refine ⟨2538026530756167049006033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3384035374341556065341377 2538026530756167049006033)
                      ·
                        rfl

theorem cell23_4942789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 8, 2].length) (baseStart_4942789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942789 prefixEnd_4942789 := by exact prefixLift 4942789
  have htrace : WordTrace (prefixWord ++ tailWord_4942789) baseStart_4942789 baseEnd_4942789 := by
    simpa [prefixWord, tailWord_4942789, baseEnd_4942789] using wordTrace_append hprefix tailTrace_4942789
  have hstable : (prefixWord ++ tailWord_4942789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942789).length < 2 ^ (prefixWord ++ tailWord_4942789).sum := by decide
  have hdescent : baseEnd_4942789 < baseStart_4942789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942790 : List Nat := [6, 1, 3, 1, 1, 1, 10]
def baseStart_4942790 : Nat := 118140960795 + 4942790 * 2 ^ 59
def prefixEnd_4942790 : Nat := 4983230072969 + 3 ^ 40 * 4942790 * 2
def baseEnd_4942790 : Nat := 31333667212800265988809

theorem tailTrace_4942790 : CollatzResearch.WordTrace tailWord_4942790 prefixEnd_4942790 31333667212800265988809 := by
  unfold tailWord_4942790
  simp only [CollatzResearch.WordTrace]
  refine ⟨5633698805097608317812307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 120185574508748977446662549 5633698805097608317812307)
  ·
    refine ⟨8450548207646412476718461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5633698805097608317812307 8450548207646412476718461)
    ·
      refine ⟨3168955577867404678769423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8450548207646412476718461 3168955577867404678769423)
      ·
        refine ⟨4753433366801107018154135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3168955577867404678769423 4753433366801107018154135)
        ·
          refine ⟨7130150050201660527231203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4753433366801107018154135 7130150050201660527231203)
          ·
            refine ⟨10695225075302490790846805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7130150050201660527231203 10695225075302490790846805)
            ·
              refine ⟨31333667212800265988809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10695225075302490790846805 31333667212800265988809)
              ·
                rfl

theorem cell23_4942790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 10].length) (baseStart_4942790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942790 prefixEnd_4942790 := by exact prefixLift 4942790
  have htrace : WordTrace (prefixWord ++ tailWord_4942790) baseStart_4942790 baseEnd_4942790 := by
    simpa [prefixWord, tailWord_4942790, baseEnd_4942790] using wordTrace_append hprefix tailTrace_4942790
  have hstable : (prefixWord ++ tailWord_4942790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942790).length < 2 ^ (prefixWord ++ tailWord_4942790).sum := by decide
  have hdescent : baseEnd_4942790 < baseStart_4942790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942819 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 4]
def baseStart_4942819 : Nat := 118140960795 + 4942819 * 2 ^ 59
def prefixEnd_4942819 : Nat := 4983230072969 + 3 ^ 40 * 4942819 * 2
def baseEnd_4942819 : Nat := 2538041935175801931630895

theorem tailTrace_4942819 : CollatzResearch.WordTrace tailWord_4942819 prefixEnd_4942819 2538041935175801931630895 := by
  unfold tailWord_4942819
  simp only [CollatzResearch.WordTrace]
  refine ⟨180279419480018404122799511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120186279653345602748533007 180279419480018404122799511)
  ·
    refine ⟨270419129220027606184199267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180279419480018404122799511 270419129220027606184199267)
    ·
      refine ⟨405628693830041409276298901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270419129220027606184199267 405628693830041409276298901)
      ·
        refine ⟨19013845023283191059826511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 405628693830041409276298901 19013845023283191059826511)
        ·
          refine ⟨28520767534924786589739767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19013845023283191059826511 28520767534924786589739767)
          ·
            refine ⟨42781151302387179884609651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28520767534924786589739767 42781151302387179884609651)
            ·
              refine ⟨64171726953580769826914477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42781151302387179884609651 64171726953580769826914477)
              ·
                refine ⟨24064397607592788685092929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64171726953580769826914477 24064397607592788685092929)
                ·
                  refine ⟨18048298205694591513819697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24064397607592788685092929 18048298205694591513819697)
                  ·
                    refine ⟨13536223654270943635364773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18048298205694591513819697 13536223654270943635364773)
                    ·
                      refine ⟨2538041935175801931630895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13536223654270943635364773 2538041935175801931630895)
                      ·
                        rfl

theorem cell23_4942819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_4942819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942819 prefixEnd_4942819 := by exact prefixLift 4942819
  have htrace : WordTrace (prefixWord ++ tailWord_4942819) baseStart_4942819 baseEnd_4942819 := by
    simpa [prefixWord, tailWord_4942819, baseEnd_4942819] using wordTrace_append hprefix tailTrace_4942819
  have hstable : (prefixWord ++ tailWord_4942819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942819).length < 2 ^ (prefixWord ++ tailWord_4942819).sum := by decide
  have hdescent : baseEnd_4942819 < baseStart_4942819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942823 : List Nat := [1, 1, 5, 2, 2, 1, 3, 1, 1, 4, 2]
def baseStart_4942823 : Nat := 118140960795 + 4942823 * 2 ^ 59
def prefixEnd_4942823 : Nat := 4983230072969 + 3 ^ 40 * 4942823 * 2
def baseEnd_4942823 : Nat := 2538043989098419915980877

theorem tailTrace_4942823 : CollatzResearch.WordTrace tailWord_4942823 prefixEnd_4942823 2538043989098419915980877 := by
  unfold tailWord_4942823
  simp only [CollatzResearch.WordTrace]
  refine ⟨180279565372003912805945123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120186376914669275203963415 180279565372003912805945123)
  ·
    refine ⟨270419348058005869208917685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180279565372003912805945123 270419348058005869208917685)
    ·
      refine ⟨25351813880438050238336033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 270419348058005869208917685 25351813880438050238336033)
      ·
        refine ⟨19013860410328537678752025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25351813880438050238336033 19013860410328537678752025)
        ·
          refine ⟨14260395307746403259064019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19013860410328537678752025 14260395307746403259064019)
          ·
            refine ⟨21390592961619604888596029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14260395307746403259064019 21390592961619604888596029)
            ·
              refine ⟨8021472360607351833223511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21390592961619604888596029 8021472360607351833223511)
              ·
                refine ⟨12032208540911027749835267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8021472360607351833223511 12032208540911027749835267)
                ·
                  refine ⟨18048312811366541624752901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12032208540911027749835267 18048312811366541624752901)
                  ·
                    refine ⟨3384058652131226554641169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18048312811366541624752901 3384058652131226554641169)
                    ·
                      refine ⟨2538043989098419915980877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3384058652131226554641169 2538043989098419915980877)
                      ·
                        rfl

theorem cell23_4942823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_4942823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942823 prefixEnd_4942823 := by exact prefixLift 4942823
  have htrace : WordTrace (prefixWord ++ tailWord_4942823) baseStart_4942823 baseEnd_4942823 := by
    simpa [prefixWord, tailWord_4942823, baseEnd_4942823] using wordTrace_append hprefix tailTrace_4942823
  have hstable : (prefixWord ++ tailWord_4942823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942823).length < 2 ^ (prefixWord ++ tailWord_4942823).sum := by decide
  have hdescent : baseEnd_4942823 < baseStart_4942823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942859 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 4, 5]
def baseStart_4942859 : Nat := 118140960795 + 4942859 * 2 ^ 59
def prefixEnd_4942859 : Nat := 4983230072969 + 3 ^ 40 * 4942859 * 2
def baseEnd_4942859 : Nat := 846020824800660591710237

theorem tailTrace_4942859 : CollatzResearch.WordTrace tailWord_4942859 prefixEnd_4942859 846020824800660591710237 := by
  unfold tailWord_4942859
  simp only [CollatzResearch.WordTrace]
  refine ⟨180280878399873490954255631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120187252266582327302837087 180280878399873490954255631)
  ·
    refine ⟨270421317599810236431383447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180280878399873490954255631 270421317599810236431383447)
    ·
      refine ⟨405631976399715354647075171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270421317599810236431383447 405631976399715354647075171)
      ·
        refine ⟨608447964599573031970612757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405631976399715354647075171 608447964599573031970612757)
        ·
          refine ⟨28520998340604985873622473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 608447964599573031970612757 28520998340604985873622473)
          ·
            refine ⟨21390748755453739405216855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28520998340604985873622473 21390748755453739405216855)
            ·
              refine ⟨32086123133180609107825283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21390748755453739405216855 32086123133180609107825283)
              ·
                refine ⟨48129184699770913661737925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32086123133180609107825283 48129184699770913661737925)
                ·
                  refine ⟨9024222131207046311575861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48129184699770913661737925 9024222131207046311575861)
                  ·
                    refine ⟨846020824800660591710237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9024222131207046311575861 846020824800660591710237)
                    ·
                      rfl

theorem cell23_4942859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 5].length) (baseStart_4942859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942859 prefixEnd_4942859 := by exact prefixLift 4942859
  have htrace : WordTrace (prefixWord ++ tailWord_4942859) baseStart_4942859 baseEnd_4942859 := by
    simpa [prefixWord, tailWord_4942859, baseEnd_4942859] using wordTrace_append hprefix tailTrace_4942859
  have hstable : (prefixWord ++ tailWord_4942859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942859).length < 2 ^ (prefixWord ++ tailWord_4942859).sum := by decide
  have hdescent : baseEnd_4942859 < baseStart_4942859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942869 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_4942869 : Nat := 118140960795 + 4942869 * 2 ^ 59
def prefixEnd_4942869 : Nat := 4983230072969 + 3 ^ 40 * 4942869 * 2
def baseEnd_4942869 : Nat := 2538067609208526736005665

theorem tailTrace_4942869 : CollatzResearch.WordTrace tailWord_4942869 prefixEnd_4942869 2538067609208526736005665 := by
  unfold tailWord_4942869
  simp only [CollatzResearch.WordTrace]
  refine ⟨180281243129837262662119661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120187495419891508441413107 180281243129837262662119661)
  ·
    refine ⟨67605466173688973498294873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180281243129837262662119661 67605466173688973498294873)
    ·
      refine ⟨50704099630266730123721155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67605466173688973498294873 50704099630266730123721155)
      ·
        refine ⟨76056149445400095185581733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50704099630266730123721155 76056149445400095185581733)
        ·
          refine ⟨14260528021012517847296575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76056149445400095185581733 14260528021012517847296575)
          ·
            refine ⟨21390792031518776770944863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14260528021012517847296575 21390792031518776770944863)
            ·
              refine ⟨32086188047278165156417295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21390792031518776770944863 32086188047278165156417295)
              ·
                refine ⟨48129282070917247734625943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32086188047278165156417295 48129282070917247734625943)
                ·
                  refine ⟨72193923106375871601938915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48129282070917247734625943 72193923106375871601938915)
                  ·
                    refine ⟨108290884659563807402908373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72193923106375871601938915 108290884659563807402908373)
                    ·
                      refine ⟨2538067609208526736005665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108290884659563807402908373 2538067609208526736005665)
                      ·
                        rfl

theorem cell23_4942869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_4942869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942869 prefixEnd_4942869 := by exact prefixLift 4942869
  have htrace : WordTrace (prefixWord ++ tailWord_4942869) baseStart_4942869 baseEnd_4942869 := by
    simpa [prefixWord, tailWord_4942869, baseEnd_4942869] using wordTrace_append hprefix tailTrace_4942869
  have hstable : (prefixWord ++ tailWord_4942869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942869).length < 2 ^ (prefixWord ++ tailWord_4942869).sum := by decide
  have hdescent : baseEnd_4942869 < baseStart_4942869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942896 : List Nat := [2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 4]
def baseStart_4942896 : Nat := 118140960795 + 4942896 * 2 ^ 59
def prefixEnd_4942896 : Nat := 4983230072969 + 3 ^ 40 * 4942896 * 2
def baseEnd_4942896 : Nat := 2538081473186198130368041

theorem tailTrace_4942896 : CollatzResearch.WordTrace tailWord_4942896 prefixEnd_4942896 2538081473186198130368041 := by
  unfold tailWord_4942896
  simp only [CollatzResearch.WordTrace]
  refine ⟨90141113950369723136676271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120188151933826297515568361 90141113950369723136676271)
  ·
    refine ⟨135211670925554584705014407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90141113950369723136676271 135211670925554584705014407)
    ·
      refine ⟨202817506388331877057521611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135211670925554584705014407 202817506388331877057521611)
      ·
        refine ⟨304226259582497815586282417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202817506388331877057521611 304226259582497815586282417)
        ·
          refine ⟨228169694686873361689711813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304226259582497815586282417 228169694686873361689711813)
          ·
            refine ⟨42781817753788755316820965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228169694686873361689711813 42781817753788755316820965)
            ·
              refine ⟨8021590828835391621903931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42781817753788755316820965 8021590828835391621903931)
              ·
                refine ⟨12032386243253087432855897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8021590828835391621903931 12032386243253087432855897)
                ·
                  refine ⟨9024289682439815574641923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12032386243253087432855897 9024289682439815574641923)
                  ·
                    refine ⟨13536434523659723361962885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9024289682439815574641923 13536434523659723361962885)
                    ·
                      refine ⟨2538081473186198130368041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13536434523659723361962885 2538081473186198130368041)
                      ·
                        rfl

theorem cell23_4942896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 4].length) (baseStart_4942896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942896 prefixEnd_4942896 := by exact prefixLift 4942896
  have htrace : WordTrace (prefixWord ++ tailWord_4942896) baseStart_4942896 baseEnd_4942896 := by
    simpa [prefixWord, tailWord_4942896, baseEnd_4942896] using wordTrace_append hprefix tailTrace_4942896
  have hstable : (prefixWord ++ tailWord_4942896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942896).length < 2 ^ (prefixWord ++ tailWord_4942896).sum := by decide
  have hdescent : baseEnd_4942896 < baseStart_4942896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942973 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 4, 3, 2]
def baseStart_4942973 : Nat := 118140960795 + 4942973 * 2 ^ 59
def prefixEnd_4942973 : Nat := 4983230072969 + 3 ^ 40 * 4942973 * 2
def baseEnd_4942973 : Nat := 2538121011196594329105187

theorem tailTrace_4942973 : CollatzResearch.WordTrace tailWord_4942973 prefixEnd_4942973 2538121011196594329105187 := by
  unfold tailWord_4942973
  simp only [CollatzResearch.WordTrace]
  refine ⟨180285036321460488423905573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120190024214306992282603715 180285036321460488423905573)
  ·
    refine ⟨33803444310273841579482295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180285036321460488423905573 33803444310273841579482295)
    ·
      refine ⟨50705166465410762369223443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33803444310273841579482295 50705166465410762369223443)
      ·
        refine ⟨76057749698116143553835165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50705166465410762369223443 76057749698116143553835165)
        ·
          refine ⟨28521656136793553832688187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76057749698116143553835165 28521656136793553832688187)
          ·
            refine ⟨42782484205190330749032281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28521656136793553832688187 42782484205190330749032281)
            ·
              refine ⟨32086863153892748061774211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42782484205190330749032281 32086863153892748061774211)
              ·
                refine ⟨48130294730839122092661317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32086863153892748061774211 48130294730839122092661317)
                ·
                  refine ⟨9024430262032335392373997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48130294730839122092661317 9024430262032335392373997)
                  ·
                    refine ⟨3384161348262125772140249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9024430262032335392373997 3384161348262125772140249)
                    ·
                      refine ⟨2538121011196594329105187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3384161348262125772140249 2538121011196594329105187)
                      ·
                        rfl

theorem cell23_4942973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_4942973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942973 prefixEnd_4942973 := by exact prefixLift 4942973
  have htrace : WordTrace (prefixWord ++ tailWord_4942973) baseStart_4942973 baseEnd_4942973 := by
    simpa [prefixWord, tailWord_4942973, baseEnd_4942973] using wordTrace_append hprefix tailTrace_4942973
  have hstable : (prefixWord ++ tailWord_4942973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942973).length < 2 ^ (prefixWord ++ tailWord_4942973).sum := by decide
  have hdescent : baseEnd_4942973 < baseStart_4942973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942974 : List Nat := [4, 2, 4, 1, 1, 1, 2, 1, 3, 4]
def baseStart_4942974 : Nat := 118140960795 + 4942974 * 2 ^ 59
def prefixEnd_4942974 : Nat := 4983230072969 + 3 ^ 40 * 4942974 * 2
def baseEnd_4942974 : Nat := 846040508225749608397561

theorem tailTrace_4942974 : CollatzResearch.WordTrace tailWord_4942974 prefixEnd_4942974 846040508225749608397561 := by
  unfold tailWord_4942974
  simp only [CollatzResearch.WordTrace]
  refine ⟨22535634099307108199336497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120190048529637910396461317 22535634099307108199336497)
  ·
    refine ⟨16901725574480331149502373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22535634099307108199336497 16901725574480331149502373)
    ·
      refine ⟨3169073545215062090531695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16901725574480331149502373 3169073545215062090531695)
      ·
        refine ⟨4753610317822593135797543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3169073545215062090531695 4753610317822593135797543)
        ·
          refine ⟨7130415476733889703696315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4753610317822593135797543 7130415476733889703696315)
          ·
            refine ⟨10695623215100834555544473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7130415476733889703696315 10695623215100834555544473)
            ·
              refine ⟨8021717411325625916658355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10695623215100834555544473 8021717411325625916658355)
              ·
                refine ⟨12032576116988438874987533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8021717411325625916658355 12032576116988438874987533)
                ·
                  refine ⟨4512216043870664578120325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12032576116988438874987533 4512216043870664578120325)
                  ·
                    refine ⟨846040508225749608397561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4512216043870664578120325 846040508225749608397561)
                    ·
                      rfl

theorem cell23_4942974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_4942974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942974 prefixEnd_4942974 := by exact prefixLift 4942974
  have htrace : WordTrace (prefixWord ++ tailWord_4942974) baseStart_4942974 baseEnd_4942974 := by
    simpa [prefixWord, tailWord_4942974, baseEnd_4942974] using wordTrace_append hprefix tailTrace_4942974
  have hstable : (prefixWord ++ tailWord_4942974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942974).length < 2 ^ (prefixWord ++ tailWord_4942974).sum := by decide
  have hdescent : baseEnd_4942974 < baseStart_4942974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942980 : List Nat := [2, 3, 2, 1, 2, 3, 2, 1, 3, 1, 3]
def baseStart_4942980 : Nat := 118140960795 + 4942980 * 2 ^ 59
def prefixEnd_4942980 : Nat := 4983230072969 + 3 ^ 40 * 4942980 * 2
def baseEnd_4942980 : Nat := 2538124605561175801717655

theorem tailTrace_4942980 : CollatzResearch.WordTrace tailWord_4942980 prefixEnd_4942980 2538124605561175801717655 := by
  unfold tailWord_4942980
  simp only [CollatzResearch.WordTrace]
  refine ⟨90142645816217564309705197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120190194421623419079606929 90142645816217564309705197)
  ·
    refine ⟨33803492181081586616139449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90142645816217564309705197 33803492181081586616139449)
    ·
      refine ⟨25352619135811189962104587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33803492181081586616139449 25352619135811189962104587)
      ·
        refine ⟨38028928703716784943156881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25352619135811189962104587 38028928703716784943156881)
        ·
          refine ⟨28521696527787588707367661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38028928703716784943156881 28521696527787588707367661)
          ·
            refine ⟨10695636197920345765262873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28521696527787588707367661 10695636197920345765262873)
            ·
              refine ⟨8021727148440259323947155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10695636197920345765262873 8021727148440259323947155)
              ·
                refine ⟨12032590722660388985920733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8021727148440259323947155 12032590722660388985920733)
                ·
                  refine ⟨4512221520997645869720275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12032590722660388985920733 4512221520997645869720275)
                  ·
                    refine ⟨6768332281496468804580413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4512221520997645869720275 6768332281496468804580413)
                    ·
                      refine ⟨2538124605561175801717655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6768332281496468804580413 2538124605561175801717655)
                      ·
                        rfl

theorem cell23_4942980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_4942980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942980 prefixEnd_4942980 := by exact prefixLift 4942980
  have htrace : WordTrace (prefixWord ++ tailWord_4942980) baseStart_4942980 baseEnd_4942980 := by
    simpa [prefixWord, tailWord_4942980, baseEnd_4942980] using wordTrace_append hprefix tailTrace_4942980
  have hstable : (prefixWord ++ tailWord_4942980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942980).length < 2 ^ (prefixWord ++ tailWord_4942980).sum := by decide
  have hdescent : baseEnd_4942980 < baseStart_4942980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943023 : List Nat := [1, 1, 2, 1, 2, 3, 4, 3, 1, 2, 3]
def baseStart_4943023 : Nat := 118140960795 + 4943023 * 2 ^ 59
def prefixEnd_4943023 : Nat := 4983230072969 + 3 ^ 40 * 4943023 * 2
def baseEnd_4943023 : Nat := 2538146685229319133479957

theorem tailTrace_4943023 : CollatzResearch.WordTrace tailWord_4943023 prefixEnd_4943023 2538146685229319133479957 := by
  unfold tailWord_4943023
  simp only [CollatzResearch.WordTrace]
  refine ⟨180286859971279346963225723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120191239980852897975483815 180286859971279346963225723)
  ·
    refine ⟨270430289956919020444838585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180286859971279346963225723 270430289956919020444838585)
    ·
      refine ⟨202822717467689265333628939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270430289956919020444838585 202822717467689265333628939)
      ·
        refine ⟨304234076201533898000443409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202822717467689265333628939 304234076201533898000443409)
        ·
          refine ⟨228175557151150423500332557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304234076201533898000443409 228175557151150423500332557)
          ·
            refine ⟨85565833931681408812624709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228175557151150423500332557 85565833931681408812624709)
            ·
              refine ⟨16043593862190264152367133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85565833931681408812624709 16043593862190264152367133)
              ·
                refine ⟨6016347698321349057137675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16043593862190264152367133 6016347698321349057137675)
                ·
                  refine ⟨9024521547482023585706513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6016347698321349057137675 9024521547482023585706513)
                  ·
                    refine ⟨6768391160611517689279885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9024521547482023585706513 6768391160611517689279885)
                    ·
                      refine ⟨2538146685229319133479957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6768391160611517689279885 2538146685229319133479957)
                      ·
                        rfl

theorem cell23_4943023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 2, 3].length) (baseStart_4943023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943023 prefixEnd_4943023 := by exact prefixLift 4943023
  have htrace : WordTrace (prefixWord ++ tailWord_4943023) baseStart_4943023 baseEnd_4943023 := by
    simpa [prefixWord, tailWord_4943023, baseEnd_4943023] using wordTrace_append hprefix tailTrace_4943023
  have hstable : (prefixWord ++ tailWord_4943023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943023).length < 2 ^ (prefixWord ++ tailWord_4943023).sum := by decide
  have hdescent : baseEnd_4943023 < baseStart_4943023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943026 : List Nat := [3, 2, 1, 1, 1, 6, 9]
def baseStart_4943026 : Nat := 118140960795 + 4943026 * 2 ^ 59
def prefixEnd_4943026 : Nat := 4983230072969 + 3 ^ 40 * 4943026 * 2
def baseEnd_4943026 : Nat := 31335163279892378046203

theorem tailTrace_4943026 : CollatzResearch.WordTrace tailWord_4943026 prefixEnd_4943026 31335163279892378046203 := by
  unfold tailWord_4943026
  simp only [CollatzResearch.WordTrace]
  refine ⟨45071742347567119618896233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120191312926845652317056621 45071742347567119618896233)
  ·
    refine ⟨33803806760675339714172175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45071742347567119618896233 33803806760675339714172175)
    ·
      refine ⟨50705710141013009571258263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33803806760675339714172175 50705710141013009571258263)
      ·
        refine ⟨76058565211519514356887395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50705710141013009571258263 76058565211519514356887395)
        ·
          refine ⟨114087847817279271535331093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76058565211519514356887395 114087847817279271535331093)
          ·
            refine ⟨5347867866434965853218645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 114087847817279271535331093 5347867866434965853218645)
            ·
              refine ⟨31335163279892378046203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5347867866434965853218645 31335163279892378046203)
              ·
                rfl

theorem cell23_4943026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 9].length) (baseStart_4943026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943026 prefixEnd_4943026 := by exact prefixLift 4943026
  have htrace : WordTrace (prefixWord ++ tailWord_4943026) baseStart_4943026 baseEnd_4943026 := by
    simpa [prefixWord, tailWord_4943026, baseEnd_4943026] using wordTrace_append hprefix tailTrace_4943026
  have hstable : (prefixWord ++ tailWord_4943026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943026).length < 2 ^ (prefixWord ++ tailWord_4943026).sum := by decide
  have hdescent : baseEnd_4943026 < baseStart_4943026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943037 : List Nat := [1, 4, 1, 2, 1, 1, 2, 6, 1, 2, 2]
def baseStart_4943037 : Nat := 118140960795 + 4943037 * 2 ^ 59
def prefixEnd_4943037 : Nat := 4983230072969 + 3 ^ 40 * 4943037 * 2
def baseEnd_4943037 : Nat := 2538153873958482078704893

theorem tailTrace_4943037 : CollatzResearch.WordTrace tailWord_4943037 prefixEnd_4943037 2538153873958482078704893 := by
  unfold tailWord_4943037
  simp only [CollatzResearch.WordTrace]
  refine ⟨180287370593228627354235365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120191580395485751569490243 180287370593228627354235365)
  ·
    refine ⟨33803881986230367628919131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180287370593228627354235365 33803881986230367628919131)
    ·
      refine ⟨50705822979345551443378697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33803881986230367628919131 50705822979345551443378697)
      ·
        refine ⟨38029367234509163582534023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50705822979345551443378697 38029367234509163582534023)
        ·
          refine ⟨57044050851763745373801035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38029367234509163582534023 57044050851763745373801035)
          ·
            refine ⟨85566076277645618060701553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57044050851763745373801035 85566076277645618060701553)
            ·
              refine ⟨64174557208234213545526165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85566076277645618060701553 64174557208234213545526165)
              ·
                refine ⟨3008182369135978759946539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64174557208234213545526165 3008182369135978759946539)
                ·
                  refine ⟨4512273553703968139919809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3008182369135978759946539 4512273553703968139919809)
                  ·
                    refine ⟨3384205165277976104939857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4512273553703968139919809 3384205165277976104939857)
                    ·
                      refine ⟨2538153873958482078704893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3384205165277976104939857 2538153873958482078704893)
                      ·
                        rfl

theorem cell23_4943037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_4943037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943037 prefixEnd_4943037 := by exact prefixLift 4943037
  have htrace : WordTrace (prefixWord ++ tailWord_4943037) baseStart_4943037 baseEnd_4943037 := by
    simpa [prefixWord, tailWord_4943037, baseEnd_4943037] using wordTrace_append hprefix tailTrace_4943037
  have hstable : (prefixWord ++ tailWord_4943037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943037).length < 2 ^ (prefixWord ++ tailWord_4943037).sum := by decide
  have hdescent : baseEnd_4943037 < baseStart_4943037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943087 : List Nat := [1, 1, 2, 1, 7, 1, 2, 2, 2, 1, 3]
def baseStart_4943087 : Nat := 118140960795 + 4943087 * 2 ^ 59
def prefixEnd_4943087 : Nat := 4983230072969 + 3 ^ 40 * 4943087 * 2
def baseEnd_4943087 : Nat := 2538179547991206883079663

theorem tailTrace_4943087 : CollatzResearch.WordTrace tailWord_4943087 prefixEnd_4943087 2538179547991206883079663 := by
  unfold tailWord_4943087
  simp only [CollatzResearch.WordTrace]
  refine ⟨180289194243047485893555515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120192796162031657262370343 180289194243047485893555515)
  ·
    refine ⟨270433791364571228840333273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180289194243047485893555515 270433791364571228840333273)
    ·
      refine ⟨202825343523428421630249955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270433791364571228840333273 202825343523428421630249955)
      ·
        refine ⟨304238015285142632445374933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202825343523428421630249955 304238015285142632445374933)
        ·
          refine ⟨7130578483245530447938475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 304238015285142632445374933 7130578483245530447938475)
          ·
            refine ⟨10695867724868295671907713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7130578483245530447938475 10695867724868295671907713)
            ·
              refine ⟨8021900793651221753930785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10695867724868295671907713 8021900793651221753930785)
              ·
                refine ⟨6016425595238416315448089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8021900793651221753930785 6016425595238416315448089)
                ·
                  refine ⟨4512319196428812236586067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6016425595238416315448089 4512319196428812236586067)
                  ·
                    refine ⟨6768478794643218354879101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4512319196428812236586067 6768478794643218354879101)
                    ·
                      refine ⟨2538179547991206883079663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6768478794643218354879101 2538179547991206883079663)
                      ·
                        rfl

theorem cell23_4943087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 1, 3].length) (baseStart_4943087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943087 prefixEnd_4943087 := by exact prefixLift 4943087
  have htrace : WordTrace (prefixWord ++ tailWord_4943087) baseStart_4943087 baseEnd_4943087 := by
    simpa [prefixWord, tailWord_4943087, baseEnd_4943087] using wordTrace_append hprefix tailTrace_4943087
  have hstable : (prefixWord ++ tailWord_4943087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943087).length < 2 ^ (prefixWord ++ tailWord_4943087).sum := by decide
  have hdescent : baseEnd_4943087 < baseStart_4943087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943116 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 9]
def baseStart_4943116 : Nat := 118140960795 + 4943116 * 2 ^ 59
def prefixEnd_4943116 : Nat := 4983230072969 + 3 ^ 40 * 4943116 * 2
def baseEnd_4943116 : Nat := 282021604325576363290781

theorem tailTrace_4943116 : CollatzResearch.WordTrace tailWord_4943116 prefixEnd_4943116 282021604325576363290781 := by
  unfold tailWord_4943116
  simp only [CollatzResearch.WordTrace]
  refine ⟨90145125979971211923180601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120193501306628282564240801 90145125979971211923180601)
  ·
    refine ⟨67608844484978408942385451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90145125979971211923180601 67608844484978408942385451)
    ·
      refine ⟨101413266727467613413578177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67608844484978408942385451 101413266727467613413578177)
      ·
        refine ⟨76059950045600710060183633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101413266727467613413578177 76059950045600710060183633)
        ·
          refine ⟨57044962534200532545137725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76059950045600710060183633 57044962534200532545137725)
          ·
            refine ⟨21391860950325199704426647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57044962534200532545137725 21391860950325199704426647)
            ·
              refine ⟨32087791425487799556639971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21391860950325199704426647 32087791425487799556639971)
              ·
                refine ⟨48131687138231699334959957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32087791425487799556639971 48131687138231699334959957)
                ·
                  refine ⟨282021604325576363290781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48131687138231699334959957 282021604325576363290781)
                  ·
                    rfl

theorem cell23_4943116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 9].length) (baseStart_4943116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943116 prefixEnd_4943116 := by exact prefixLift 4943116
  have htrace : WordTrace (prefixWord ++ tailWord_4943116) baseStart_4943116 baseEnd_4943116 := by
    simpa [prefixWord, tailWord_4943116, baseEnd_4943116] using wordTrace_append hprefix tailTrace_4943116
  have hstable : (prefixWord ++ tailWord_4943116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943116).length < 2 ^ (prefixWord ++ tailWord_4943116).sum := by decide
  have hdescent : baseEnd_4943116 < baseStart_4943116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943144 : List Nat := [2, 1, 5, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_4943144 : Nat := 118140960795 + 4943144 * 2 ^ 59
def prefixEnd_4943144 : Nat := 4983230072969 + 3 ^ 40 * 4943144 * 2
def baseEnd_4943144 : Nat := 2538208816388513160066901

theorem tailTrace_4943144 : CollatzResearch.WordTrace tailWord_4943144 prefixEnd_4943144 2538208816388513160066901 := by
  unfold tailWord_4943144
  simp only [CollatzResearch.WordTrace]
  refine ⟨90145636601920492314190243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120194182135893989752253657 90145636601920492314190243)
  ·
    refine ⟨135218454902880738471285365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90145636601920492314190243 135218454902880738471285365)
    ·
      refine ⟨12676730147145069231683003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135218454902880738471285365 12676730147145069231683003)
      ·
        refine ⟨19015095220717603847524505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12676730147145069231683003 19015095220717603847524505)
        ·
          refine ⟨14261321415538202885643379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19015095220717603847524505 14261321415538202885643379)
          ·
            refine ⟨21391982123307304328465069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14261321415538202885643379 21391982123307304328465069)
            ·
              refine ⟨8021993296240239123174401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21391982123307304328465069 8021993296240239123174401)
              ·
                refine ⟨6016494972180179342380801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8021993296240239123174401 6016494972180179342380801)
                ·
                  refine ⟨4512371229135134506785601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6016494972180179342380801 4512371229135134506785601)
                  ·
                    refine ⟨3384278421851350880089201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4512371229135134506785601 3384278421851350880089201)
                    ·
                      refine ⟨2538208816388513160066901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3384278421851350880089201 2538208816388513160066901)
                      ·
                        rfl

theorem cell23_4943144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_4943144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943144 prefixEnd_4943144 := by exact prefixLift 4943144
  have htrace : WordTrace (prefixWord ++ tailWord_4943144) baseStart_4943144 baseEnd_4943144 := by
    simpa [prefixWord, tailWord_4943144, baseEnd_4943144] using wordTrace_append hprefix tailTrace_4943144
  have hstable : (prefixWord ++ tailWord_4943144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943144).length < 2 ^ (prefixWord ++ tailWord_4943144).sum := by decide
  have hdescent : baseEnd_4943144 < baseStart_4943144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943161 : List Nat := [1, 2, 1, 6, 2, 1, 3, 1, 2, 2, 2]
def baseStart_4943161 : Nat := 118140960795 + 4943161 * 2 ^ 59
def prefixEnd_4943161 : Nat := 4983230072969 + 3 ^ 40 * 4943161 * 2
def baseEnd_4943161 : Nat := 2538217545559639593554323

theorem tailTrace_4943161 : CollatzResearch.WordTrace tailWord_4943161 prefixEnd_4943161 2538217545559639593554323 := by
  unfold tailWord_4943161
  simp only [CollatzResearch.WordTrace]
  refine ⟨180291893244779396531749337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120194595496519597687832891 180291893244779396531749337)
  ·
    refine ⟨135218919933584547398812003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180291893244779396531749337 135218919933584547398812003)
    ·
      refine ⟨202828379900376821098218005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135218919933584547398812003 202828379900376821098218005)
      ·
        refine ⟨9507580307830163488978969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 202828379900376821098218005 9507580307830163488978969)
        ·
          refine ⟨7130685230872622616734227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9507580307830163488978969 7130685230872622616734227)
          ·
            refine ⟨10696027846308933925101341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7130685230872622616734227 10696027846308933925101341)
            ·
              refine ⟨4011010442365850221913003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10696027846308933925101341 4011010442365850221913003)
              ·
                refine ⟨6016515663548775332869505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4011010442365850221913003 6016515663548775332869505)
                ·
                  refine ⟨4512386747661581499652129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6016515663548775332869505 4512386747661581499652129)
                  ·
                    refine ⟨3384290060746186124739097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4512386747661581499652129 3384290060746186124739097)
                    ·
                      refine ⟨2538217545559639593554323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3384290060746186124739097 2538217545559639593554323)
                      ·
                        rfl

theorem cell23_4943161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_4943161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943161 prefixEnd_4943161 := by exact prefixLift 4943161
  have htrace : WordTrace (prefixWord ++ tailWord_4943161) baseStart_4943161 baseEnd_4943161 := by
    simpa [prefixWord, tailWord_4943161, baseEnd_4943161] using wordTrace_append hprefix tailTrace_4943161
  have hstable : (prefixWord ++ tailWord_4943161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943161).length < 2 ^ (prefixWord ++ tailWord_4943161).sum := by decide
  have hdescent : baseEnd_4943161 < baseStart_4943161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943176 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 1, 10]
def baseStart_4943176 : Nat := 118140960795 + 4943176 * 2 ^ 59
def prefixEnd_4943176 : Nat := 4983230072969 + 3 ^ 40 * 4943176 * 2
def baseEnd_4943176 : Nat := 846075082589819011622251

theorem tailTrace_4943176 : CollatzResearch.WordTrace tailWord_4943176 prefixEnd_4943176 846075082589819011622251 := by
  unfold tailWord_4943176
  simp only [CollatzResearch.WordTrace]
  refine ⟨90146220169862527046772691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120194960226483369395696921 90146220169862527046772691)
  ·
    refine ⟨135219330254793790570159037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90146220169862527046772691 135219330254793790570159037)
    ·
      refine ⟨50707248845547671463809639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135219330254793790570159037 50707248845547671463809639)
      ·
        refine ⟨76060873268321507195714459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50707248845547671463809639 76060873268321507195714459)
        ·
          refine ⟨114091309902482260793571689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76060873268321507195714459 114091309902482260793571689)
          ·
            refine ⟨85568482426861695595178767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114091309902482260793571689 85568482426861695595178767)
            ·
              refine ⟨128352723640292543392768151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85568482426861695595178767 128352723640292543392768151)
              ·
                refine ⟨192529085460438815089152227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128352723640292543392768151 192529085460438815089152227)
                ·
                  refine ⟨288793628190658222633728341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192529085460438815089152227 288793628190658222633728341)
                  ·
                    refine ⟨846075082589819011622251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 288793628190658222633728341 846075082589819011622251)
                    ·
                      rfl

theorem cell23_4943176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_4943176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943176 prefixEnd_4943176 := by exact prefixLift 4943176
  have htrace : WordTrace (prefixWord ++ tailWord_4943176) baseStart_4943176 baseEnd_4943176 := by
    simpa [prefixWord, tailWord_4943176, baseEnd_4943176] using wordTrace_append hprefix tailTrace_4943176
  have hstable : (prefixWord ++ tailWord_4943176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943176).length < 2 ^ (prefixWord ++ tailWord_4943176).sum := by decide
  have hdescent : baseEnd_4943176 < baseStart_4943176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943193 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 5, 4]
def baseStart_4943193 : Nat := 118140960795 + 4943193 * 2 ^ 59
def prefixEnd_4943193 : Nat := 4983230072969 + 3 ^ 40 * 4943193 * 2
def baseEnd_4943193 : Nat := 846077992313527822784725

theorem tailTrace_4943193 : CollatzResearch.WordTrace tailWord_4943193 prefixEnd_4943193 846077992313527822784725 := by
  unfold tailWord_4943193
  simp only [CollatzResearch.WordTrace]
  refine ⟨180293060380663465996914233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120195373587108977331276155 180293060380663465996914233)
  ·
    refine ⟨135219795285497599497685675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180293060380663465996914233 135219795285497599497685675)
    ·
      refine ⟨202829692928246399246528513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135219795285497599497685675 202829692928246399246528513)
      ·
        refine ⟨152122269696184799434896385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202829692928246399246528513 152122269696184799434896385)
        ·
          refine ⟨114091702272138599576172289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152122269696184799434896385 114091702272138599576172289)
          ·
            refine ⟨85568776704103949682129217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114091702272138599576172289 85568776704103949682129217)
            ·
              refine ⟨64176582528077962261596913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85568776704103949682129217 64176582528077962261596913)
              ·
                refine ⟨48132436896058471696197685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64176582528077962261596913 48132436896058471696197685)
                ·
                  refine ⟨4512415959005481721518533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48132436896058471696197685 4512415959005481721518533)
                  ·
                    refine ⟨846077992313527822784725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4512415959005481721518533 846077992313527822784725)
                    ·
                      rfl

theorem cell23_4943193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 4].length) (baseStart_4943193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943193 prefixEnd_4943193 := by exact prefixLift 4943193
  have htrace : WordTrace (prefixWord ++ tailWord_4943193) baseStart_4943193 baseEnd_4943193 := by
    simpa [prefixWord, tailWord_4943193, baseEnd_4943193] using wordTrace_append hprefix tailTrace_4943193
  have hstable : (prefixWord ++ tailWord_4943193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943193).length < 2 ^ (prefixWord ++ tailWord_4943193).sum := by decide
  have hdescent : baseEnd_4943193 < baseStart_4943193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943200 : List Nat := [2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 4]
def baseStart_4943200 : Nat := 118140960795 + 4943200 * 2 ^ 59
def prefixEnd_4943200 : Nat := 4983230072969 + 3 ^ 40 * 4943200 * 2
def baseEnd_4943200 : Nat := 2538237571305164940966643

theorem tailTrace_4943200 : CollatzResearch.WordTrace tailWord_4943200 prefixEnd_4943200 2538237571305164940966643 := by
  unfold tailWord_4943200
  simp only [CollatzResearch.WordTrace]
  refine ⟨90146657845819053096209527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120195543794425404128279369 90146657845819053096209527)
  ·
    refine ⟨135219986768728579644314291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90146657845819053096209527 135219986768728579644314291)
    ·
      refine ⟨202829980153092869466471437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135219986768728579644314291 202829980153092869466471437)
      ·
        refine ⟨76061242557409826049926789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202829980153092869466471437 76061242557409826049926789)
        ·
          refine ⟨14261482979514342384361273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76061242557409826049926789 14261482979514342384361273)
          ·
            refine ⟨10696112234635756788270955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14261482979514342384361273 10696112234635756788270955)
            ·
              refine ⟨16044168351953635182406433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10696112234635756788270955 16044168351953635182406433)
              ·
                refine ⟨12033126263965226386804825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16044168351953635182406433 12033126263965226386804825)
                ·
                  refine ⟨9024844697973919790103619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12033126263965226386804825 9024844697973919790103619)
                  ·
                    refine ⟨13537267046960879685155429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9024844697973919790103619 13537267046960879685155429)
                    ·
                      refine ⟨2538237571305164940966643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13537267046960879685155429 2538237571305164940966643)
                      ·
                        rfl

theorem cell23_4943200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_4943200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943200 prefixEnd_4943200 := by exact prefixLift 4943200
  have htrace : WordTrace (prefixWord ++ tailWord_4943200) baseStart_4943200 baseEnd_4943200 := by
    simpa [prefixWord, tailWord_4943200, baseEnd_4943200] using wordTrace_append hprefix tailTrace_4943200
  have hstable : (prefixWord ++ tailWord_4943200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943200).length < 2 ^ (prefixWord ++ tailWord_4943200).sum := by decide
  have hdescent : baseEnd_4943200 < baseStart_4943200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943223 : List Nat := [1, 1, 3, 1, 1, 2, 5, 3, 6]
def baseStart_4943223 : Nat := 118140960795 + 4943223 * 2 ^ 59
def prefixEnd_4943223 : Nat := 4983230072969 + 3 ^ 40 * 4943223 * 2
def baseEnd_4943223 : Nat := 282027709040024261219893

theorem tailTrace_4943223 : CollatzResearch.WordTrace tailWord_4943223 prefixEnd_4943223 282027709040024261219893 := by
  unfold tailWord_4943223
  simp only [CollatzResearch.WordTrace]
  refine ⟨180294154570554781120506323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120196103047036520747004215 180294154570554781120506323)
  ·
    refine ⟨270441231855832171680759485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180294154570554781120506323 270441231855832171680759485)
    ·
      refine ⟨101415461945937064380284807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270441231855832171680759485 101415461945937064380284807)
      ·
        refine ⟨152123192918905596570427211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101415461945937064380284807 152123192918905596570427211)
        ·
          refine ⟨228184789378358394855640817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152123192918905596570427211 228184789378358394855640817)
          ·
            refine ⟨171138592033768796141730613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228184789378358394855640817 171138592033768796141730613)
            ·
              refine ⟨16044243003165824638287245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 171138592033768796141730613 16044243003165824638287245)
              ·
                refine ⟨6016591126187184239357717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16044243003165824638287245 6016591126187184239357717)
                ·
                  refine ⟨282027709040024261219893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6016591126187184239357717 282027709040024261219893)
                  ·
                    rfl

theorem cell23_4943223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 6].length) (baseStart_4943223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943223 prefixEnd_4943223 := by exact prefixLift 4943223
  have htrace : WordTrace (prefixWord ++ tailWord_4943223) baseStart_4943223 baseEnd_4943223 := by
    simpa [prefixWord, tailWord_4943223, baseEnd_4943223] using wordTrace_append hprefix tailTrace_4943223
  have hstable : (prefixWord ++ tailWord_4943223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943223).length < 2 ^ (prefixWord ++ tailWord_4943223).sum := by decide
  have hdescent : baseEnd_4943223 < baseStart_4943223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943234 : List Nat := [3, 4, 2, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_4943234 : Nat := 118140960795 + 4943234 * 2 ^ 59
def prefixEnd_4943234 : Nat := 4983230072969 + 3 ^ 40 * 4943234 * 2
def baseEnd_4943234 : Nat := 2538255029647417807941487

theorem tailTrace_4943234 : CollatzResearch.WordTrace tailWord_4943234 prefixEnd_4943234 2538255029647417807941487 := by
  unfold tailWord_4943234
  simp only [CollatzResearch.WordTrace]
  refine ⟨45073638943378732499789189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120196370515676619999437837 45073638943378732499789189)
  ·
    refine ⟨8451307301883512343710473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45073638943378732499789189 8451307301883512343710473)
    ·
      refine ⟨6338480476412634257782855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8451307301883512343710473 6338480476412634257782855)
      ·
        refine ⟨9507720714618951386674283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6338480476412634257782855 9507720714618951386674283)
        ·
          refine ⟨14261581071928427080011425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9507720714618951386674283 14261581071928427080011425)
          ·
            refine ⟨10696185803946320310008569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14261581071928427080011425 10696185803946320310008569)
            ·
              refine ⟨8022139352959740232506427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10696185803946320310008569 8022139352959740232506427)
              ·
                refine ⟨12033209029439610348759641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8022139352959740232506427 12033209029439610348759641)
                ·
                  refine ⟨9024906772079707761569731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12033209029439610348759641 9024906772079707761569731)
                  ·
                    refine ⟨13537360158119561642354597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9024906772079707761569731 13537360158119561642354597)
                    ·
                      refine ⟨2538255029647417807941487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13537360158119561642354597 2538255029647417807941487)
                      ·
                        rfl

theorem cell23_4943234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_4943234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943234 prefixEnd_4943234 := by exact prefixLift 4943234
  have htrace : WordTrace (prefixWord ++ tailWord_4943234) baseStart_4943234 baseEnd_4943234 := by
    simpa [prefixWord, tailWord_4943234, baseEnd_4943234] using wordTrace_append hprefix tailTrace_4943234
  have hstable : (prefixWord ++ tailWord_4943234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943234).length < 2 ^ (prefixWord ++ tailWord_4943234).sum := by decide
  have hdescent : baseEnd_4943234 < baseStart_4943234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943261 : List Nat := [1, 4, 2, 1, 3, 3, 2, 2, 1, 4]
def baseStart_4943261 : Nat := 118140960795 + 4943261 * 2 ^ 59
def prefixEnd_4943261 : Nat := 4983230072969 + 3 ^ 40 * 4943261 * 2
def baseEnd_4943261 : Nat := 846089631208363067434621

theorem tailTrace_4943261 : CollatzResearch.WordTrace tailWord_4943261 prefixEnd_4943261 846089631208363067434621 := by
  unfold tailWord_4943261
  simp only [CollatzResearch.WordTrace]
  refine ⟨180295540544417113610389637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120197027029611409073593091 180295540544417113610389637)
  ·
    refine ⟨33805413852078208801948057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180295540544417113610389637 33805413852078208801948057)
    ·
      refine ⟨25354060389058656601461043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33805413852078208801948057 25354060389058656601461043)
      ·
        refine ⟨38031090583587984902191565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25354060389058656601461043 38031090583587984902191565)
        ·
          refine ⟨14261658968845494338321837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38031090583587984902191565 14261658968845494338321837)
          ·
            refine ⟨5348122113317060376870689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14261658968845494338321837 5348122113317060376870689)
            ·
              refine ⟨4011091584987795282653017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5348122113317060376870689 4011091584987795282653017)
              ·
                refine ⟨3008318688740846461989763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4011091584987795282653017 3008318688740846461989763)
                ·
                  refine ⟨4512478033111269692984645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3008318688740846461989763 4512478033111269692984645)
                  ·
                    refine ⟨846089631208363067434621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4512478033111269692984645 846089631208363067434621)
                    ·
                      rfl

theorem cell23_4943261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_4943261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943261 prefixEnd_4943261 := by exact prefixLift 4943261
  have htrace : WordTrace (prefixWord ++ tailWord_4943261) baseStart_4943261 baseEnd_4943261 := by
    simpa [prefixWord, tailWord_4943261, baseEnd_4943261] using wordTrace_append hprefix tailTrace_4943261
  have hstable : (prefixWord ++ tailWord_4943261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943261).length < 2 ^ (prefixWord ++ tailWord_4943261).sum := by decide
  have hdescent : baseEnd_4943261 < baseStart_4943261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943307 : List Nat := [1, 1, 1, 1, 3, 3, 6, 1, 1, 1, 4]
def baseStart_4943307 : Nat := 118140960795 + 4943307 * 2 ^ 59
def prefixEnd_4943307 : Nat := 4983230072969 + 3 ^ 40 * 4943307 * 2
def baseEnd_4943307 : Nat := 2538292513735196022328651

theorem tailTrace_4943307 : CollatzResearch.WordTrace tailWord_4943307 prefixEnd_4943307 2538292513735196022328651 := by
  unfold tailWord_4943307
  simp only [CollatzResearch.WordTrace]
  refine ⟨180297218302250463466564175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120198145534833642311042783 180297218302250463466564175)
  ·
    refine ⟨270445827453375695199846263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180297218302250463466564175 270445827453375695199846263)
    ·
      refine ⟨405668741180063542799769395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270445827453375695199846263 405668741180063542799769395)
      ·
        refine ⟨608503111770095314199654093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405668741180063542799769395 608503111770095314199654093)
        ·
          refine ⟨228188666913785742824870285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 608503111770095314199654093 228188666913785742824870285)
          ·
            refine ⟨85570750092669653559326357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228188666913785742824870285 85570750092669653559326357)
            ·
              refine ⟨4011128910593890010593423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85570750092669653559326357 4011128910593890010593423)
              ·
                refine ⟨6016693365890835015890135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4011128910593890010593423 6016693365890835015890135)
                ·
                  refine ⟨9025040048836252523835203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6016693365890835015890135 9025040048836252523835203)
                  ·
                    refine ⟨13537560073254378785752805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9025040048836252523835203 13537560073254378785752805)
                    ·
                      refine ⟨2538292513735196022328651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13537560073254378785752805 2538292513735196022328651)
                      ·
                        rfl

theorem cell23_4943307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 1, 1, 4].length) (baseStart_4943307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943307 prefixEnd_4943307 := by exact prefixLift 4943307
  have htrace : WordTrace (prefixWord ++ tailWord_4943307) baseStart_4943307 baseEnd_4943307 := by
    simpa [prefixWord, tailWord_4943307, baseEnd_4943307] using wordTrace_append hprefix tailTrace_4943307
  have hstable : (prefixWord ++ tailWord_4943307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943307).length < 2 ^ (prefixWord ++ tailWord_4943307).sum := by decide
  have hdescent : baseEnd_4943307 < baseStart_4943307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943340 : List Nat := [2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 3]
def baseStart_4943340 : Nat := 118140960795 + 4943340 * 2 ^ 59
def prefixEnd_4943340 : Nat := 4983230072969 + 3 ^ 40 * 4943340 * 2
def baseEnd_4943340 : Nat := 2538309458596794393215999

theorem tailTrace_4943340 : CollatzResearch.WordTrace tailWord_4943340 prefixEnd_4943340 2538309458596794393215999 := by
  unfold tailWord_4943340
  simp only [CollatzResearch.WordTrace]
  refine ⟨90149210955565455051257737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120198947940753940068343649 90149210955565455051257737)
  ·
    refine ⟨67611908216674091288443303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90149210955565455051257737 67611908216674091288443303)
    ·
      refine ⟨101417862325011136932664955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67611908216674091288443303 101417862325011136932664955)
      ·
        refine ⟨152126793487516705398997433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101417862325011136932664955 152126793487516705398997433)
        ·
          refine ⟨114095095115637529049248075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152126793487516705398997433 114095095115637529049248075)
          ·
            refine ⟨171142642673456293573872113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114095095115637529049248075 171142642673456293573872113)
            ·
              refine ⟨128356982005092220180404085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171142642673456293573872113 128356982005092220180404085)
              ·
                refine ⟨12033467062977395641912883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128356982005092220180404085 12033467062977395641912883)
                ·
                  refine ⟨18050200594466093462869325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12033467062977395641912883 18050200594466093462869325)
                  ·
                    refine ⟨6768825222924785048575997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18050200594466093462869325 6768825222924785048575997)
                    ·
                      refine ⟨2538309458596794393215999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6768825222924785048575997 2538309458596794393215999)
                      ·
                        rfl

theorem cell23_4943340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_4943340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943340 prefixEnd_4943340 := by exact prefixLift 4943340
  have htrace : WordTrace (prefixWord ++ tailWord_4943340) baseStart_4943340 baseEnd_4943340 := by
    simpa [prefixWord, tailWord_4943340, baseEnd_4943340] using wordTrace_append hprefix tailTrace_4943340
  have hstable : (prefixWord ++ tailWord_4943340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943340).length < 2 ^ (prefixWord ++ tailWord_4943340).sum := by decide
  have hdescent : baseEnd_4943340 < baseStart_4943340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943343 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 2, 7]
def baseStart_4943343 : Nat := 118140960795 + 4943343 * 2 ^ 59
def prefixEnd_4943343 : Nat := 4983230072969 + 3 ^ 40 * 4943343 * 2
def baseEnd_4943343 : Nat := 846103666346252627159495

theorem tailTrace_4943343 : CollatzResearch.WordTrace tailWord_4943343 prefixEnd_4943343 846103666346252627159495 := by
  unfold tailWord_4943343
  simp only [CollatzResearch.WordTrace]
  refine ⟨180298531330120041614874683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120199020886746694409916455 180298531330120041614874683)
  ·
    refine ⟨270447796995180062422312025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180298531330120041614874683 270447796995180062422312025)
    ·
      refine ⟨202835847746385046816734019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270447796995180062422312025 202835847746385046816734019)
      ·
        refine ⟨304253771619577570225101029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202835847746385046816734019 304253771619577570225101029)
        ·
          refine ⟨57047582178670794417206443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 304253771619577570225101029 57047582178670794417206443)
          ·
            refine ⟨85571373268006191625809665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57047582178670794417206443 85571373268006191625809665)
            ·
              refine ⟨64178529951004643719357249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85571373268006191625809665 64178529951004643719357249)
              ·
                refine ⟨48133897463253482789517937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64178529951004643719357249 48133897463253482789517937)
                ·
                  refine ⟨36100423097440112092138453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48133897463253482789517937 36100423097440112092138453)
                  ·
                    refine ⟨846103666346252627159495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36100423097440112092138453 846103666346252627159495)
                    ·
                      rfl

theorem cell23_4943343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 7].length) (baseStart_4943343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943343 prefixEnd_4943343 := by exact prefixLift 4943343
  have htrace : WordTrace (prefixWord ++ tailWord_4943343) baseStart_4943343 baseEnd_4943343 := by
    simpa [prefixWord, tailWord_4943343, baseEnd_4943343] using wordTrace_append hprefix tailTrace_4943343
  have hstable : (prefixWord ++ tailWord_4943343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943343).length < 2 ^ (prefixWord ++ tailWord_4943343).sum := by decide
  have hdescent : baseEnd_4943343 < baseStart_4943343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943357 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 4, 1, 3]
def baseStart_4943357 : Nat := 118140960795 + 4943357 * 2 ^ 59
def prefixEnd_4943357 : Nat := 4983230072969 + 3 ^ 40 * 4943357 * 2
def baseEnd_4943357 : Nat := 2538318187767920826703421

theorem tailTrace_4943357 : CollatzResearch.WordTrace tailWord_4943357 prefixEnd_4943357 2538318187767920826703421 := by
  unfold tailWord_4943357
  simp only [CollatzResearch.WordTrace]
  refine ⟨180299041952069322005884325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120199361301379548003922883 180299041952069322005884325)
  ·
    refine ⟨33806070366012997876103311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180299041952069322005884325 33806070366012997876103311)
    ·
      refine ⟨50709105549019496814154967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33806070366012997876103311 50709105549019496814154967)
      ·
        refine ⟨76063658323529245221232451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50709105549019496814154967 76063658323529245221232451)
        ·
          refine ⟨114095487485293867831848677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76063658323529245221232451 114095487485293867831848677)
          ·
            refine ⟨21392903903492600218471627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114095487485293867831848677 21392903903492600218471627)
            ·
              refine ⟨32089355855238900327707441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21392903903492600218471627 32089355855238900327707441)
              ·
                refine ⟨24067016891429175245780581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32089355855238900327707441 24067016891429175245780581)
                ·
                  refine ⟨4512565667142970358583859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24067016891429175245780581 4512565667142970358583859)
                  ·
                    refine ⟨6768848500714455537875789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4512565667142970358583859 6768848500714455537875789)
                    ·
                      refine ⟨2538318187767920826703421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6768848500714455537875789 2538318187767920826703421)
                      ·
                        rfl

theorem cell23_4943357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_4943357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943357 prefixEnd_4943357 := by exact prefixLift 4943357
  have htrace : WordTrace (prefixWord ++ tailWord_4943357) baseStart_4943357 baseEnd_4943357 := by
    simpa [prefixWord, tailWord_4943357, baseEnd_4943357] using wordTrace_append hprefix tailTrace_4943357
  have hstable : (prefixWord ++ tailWord_4943357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943357).length < 2 ^ (prefixWord ++ tailWord_4943357).sum := by decide
  have hdescent : baseEnd_4943357 < baseStart_4943357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943397 : List Nat := [1, 3, 1, 2, 2, 1, 1, 5, 1, 4, 2]
def baseStart_4943397 : Nat := 118140960795 + 4943397 * 2 ^ 59
def prefixEnd_4943397 : Nat := 4983230072969 + 3 ^ 40 * 4943397 * 2
def baseEnd_4943397 : Nat := 2538338726994100670203237

theorem tailTrace_4943397 : CollatzResearch.WordTrace tailWord_4943397 prefixEnd_4943397 2538338726994100670203237 := by
  unfold tailWord_4943397
  simp only [CollatzResearch.WordTrace]
  refine ⟨180300500871924408837340445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120200333914616272558226963 180300500871924408837340445)
  ·
    refine ⟨67612687826971653314002667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180300500871924408837340445 67612687826971653314002667)
    ·
      refine ⟨101419031740457479971004001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67612687826971653314002667 101419031740457479971004001)
      ·
        refine ⟨76064273805343109978253001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101419031740457479971004001 76064273805343109978253001)
        ·
          refine ⟨57048205354007332483689751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76064273805343109978253001 57048205354007332483689751)
          ·
            refine ⟨85572308031010998725534627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57048205354007332483689751 85572308031010998725534627)
            ·
              refine ⟨128358462046516498088301941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85572308031010998725534627 128358462046516498088301941)
              ·
                refine ⟨12033605816860921695778307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128358462046516498088301941 12033605816860921695778307)
                ·
                  refine ⟨18050408725291382543667461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12033605816860921695778307 18050408725291382543667461)
                  ·
                    refine ⟨3384451635992134226937649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18050408725291382543667461 3384451635992134226937649)
                    ·
                      refine ⟨2538338726994100670203237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3384451635992134226937649 2538338726994100670203237)
                      ·
                        rfl

theorem cell23_4943397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_4943397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943397 prefixEnd_4943397 := by exact prefixLift 4943397
  have htrace : WordTrace (prefixWord ++ tailWord_4943397) baseStart_4943397 baseEnd_4943397 := by
    simpa [prefixWord, tailWord_4943397, baseEnd_4943397] using wordTrace_append hprefix tailTrace_4943397
  have hstable : (prefixWord ++ tailWord_4943397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943397).length < 2 ^ (prefixWord ++ tailWord_4943397).sum := by decide
  have hdescent : baseEnd_4943397 < baseStart_4943397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943410 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_4943410 : Nat := 118140960795 + 4943410 * 2 ^ 59
def prefixEnd_4943410 : Nat := 4983230072969 + 3 ^ 40 * 4943410 * 2
def baseEnd_4943410 : Nat := 2538345402242609119340677

theorem tailTrace_4943410 : CollatzResearch.WordTrace tailWord_4943410 prefixEnd_4943410 2538345402242609119340677 := by
  unfold tailWord_4943410
  simp only [CollatzResearch.WordTrace]
  refine ⟨45075243755219328014390921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120200650013918208038375789 45075243755219328014390921)
  ·
    refine ⟨33806432816414496010793191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45075243755219328014390921 33806432816414496010793191)
    ·
      refine ⟨50709649224621744016189787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33806432816414496010793191 50709649224621744016189787)
      ·
        refine ⟨76064473836932616024284681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50709649224621744016189787 76064473836932616024284681)
        ·
          refine ⟨57048355377699462018213511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76064473836932616024284681 57048355377699462018213511)
          ·
            refine ⟨85572533066549193027320267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57048355377699462018213511 85572533066549193027320267)
            ·
              refine ⟨128358799599823789540980401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85572533066549193027320267 128358799599823789540980401)
              ·
                refine ⟨96269099699867842155735301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128358799599823789540980401 96269099699867842155735301)
                ·
                  refine ⟨18050456193725220404200369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96269099699867842155735301 18050456193725220404200369)
                  ·
                    refine ⟨13537842145293915303150277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18050456193725220404200369 13537842145293915303150277)
                    ·
                      refine ⟨2538345402242609119340677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13537842145293915303150277 2538345402242609119340677)
                      ·
                        rfl

theorem cell23_4943410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_4943410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943410 prefixEnd_4943410 := by exact prefixLift 4943410
  have htrace : WordTrace (prefixWord ++ tailWord_4943410) baseStart_4943410 baseEnd_4943410 := by
    simpa [prefixWord, tailWord_4943410, baseEnd_4943410] using wordTrace_append hprefix tailTrace_4943410
  have hstable : (prefixWord ++ tailWord_4943410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943410).length < 2 ^ (prefixWord ++ tailWord_4943410).sum := by decide
  have hdescent : baseEnd_4943410 < baseStart_4943410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943447 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 3]
def baseStart_4943447 : Nat := 118140960795 + 4943447 * 2 ^ 59
def prefixEnd_4943447 : Nat := 4983230072969 + 3 ^ 40 * 4943447 * 2
def baseEnd_4943447 : Nat := 2538364401026825474578007

theorem tailTrace_4943447 : CollatzResearch.WordTrace tailWord_4943447 prefixEnd_4943447 2538364401026825474578007 := by
  unfold tailWord_4943447
  simp only [CollatzResearch.WordTrace]
  refine ⟨180302324521743267376660595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120201549681162178251107063 180302324521743267376660595)
  ·
    refine ⟨270453486782614901064990893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180302324521743267376660595 270453486782614901064990893)
    ·
      refine ⟨101420057543480587899371585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270453486782614901064990893 101420057543480587899371585)
      ·
        refine ⟨76065043157610440924528689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101420057543480587899371585 76065043157610440924528689)
        ·
          refine ⟨57048782368207830693396517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76065043157610440924528689 57048782368207830693396517)
          ·
            refine ⟨10696646694038968255011847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57048782368207830693396517 10696646694038968255011847)
            ·
              refine ⟨16044970041058452382517771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10696646694038968255011847 16044970041058452382517771)
              ·
                refine ⟨24067455061587678573776657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16044970041058452382517771 24067455061587678573776657)
                ·
                  refine ⟨18050591296190758930332493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24067455061587678573776657 18050591296190758930332493)
                  ·
                    refine ⟨6768971736071534598874685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18050591296190758930332493 6768971736071534598874685)
                    ·
                      refine ⟨2538364401026825474578007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6768971736071534598874685 2538364401026825474578007)
                      ·
                        rfl

theorem cell23_4943447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_4943447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943447 prefixEnd_4943447 := by exact prefixLift 4943447
  have htrace : WordTrace (prefixWord ++ tailWord_4943447) baseStart_4943447 baseEnd_4943447 := by
    simpa [prefixWord, tailWord_4943447, baseEnd_4943447] using wordTrace_append hprefix tailTrace_4943447
  have hstable : (prefixWord ++ tailWord_4943447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943447).length < 2 ^ (prefixWord ++ tailWord_4943447).sum := by decide
  have hdescent : baseEnd_4943447 < baseStart_4943447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943450 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 4, 5]
def baseStart_4943450 : Nat := 118140960795 + 4943450 * 2 ^ 59
def prefixEnd_4943450 : Nat := 4983230072969 + 3 ^ 40 * 4943450 * 2
def baseEnd_4943450 : Nat := 846121980489596320946831

theorem tailTrace_4943450 : CollatzResearch.WordTrace tailWord_4943450 prefixEnd_4943450 846121980489596320946831 := by
  unfold tailWord_4943450
  simp only [CollatzResearch.WordTrace]
  refine ⟨45075608485183099722254951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120201622627154932592679869 45075608485183099722254951)
  ·
    refine ⟨67613412727774649583382427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45075608485183099722254951 67613412727774649583382427)
    ·
      refine ⟨101420119091661974375073641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67613412727774649583382427 101420119091661974375073641)
      ·
        refine ⟨76065089318746480781305231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101420119091661974375073641 76065089318746480781305231)
        ·
          refine ⟨114097633978119721171957847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76065089318746480781305231 114097633978119721171957847)
          ·
            refine ⟨171146450967179581757936771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114097633978119721171957847 171146450967179581757936771)
            ·
              refine ⟨256719676450769372636905157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171146450967179581757936771 256719676450769372636905157)
              ·
                refine ⟨48134939334519257369419717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 256719676450769372636905157 48134939334519257369419717)
                ·
                  refine ⟨9025301125222360756766197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48134939334519257369419717 9025301125222360756766197)
                  ·
                    refine ⟨846121980489596320946831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9025301125222360756766197 846121980489596320946831)
                    ·
                      rfl

theorem cell23_4943450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_4943450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943450 prefixEnd_4943450 := by exact prefixLift 4943450
  have htrace : WordTrace (prefixWord ++ tailWord_4943450) baseStart_4943450 baseEnd_4943450 := by
    simpa [prefixWord, tailWord_4943450, baseEnd_4943450] using wordTrace_append hprefix tailTrace_4943450
  have hstable : (prefixWord ++ tailWord_4943450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943450).length < 2 ^ (prefixWord ++ tailWord_4943450).sum := by decide
  have hdescent : baseEnd_4943450 < baseStart_4943450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943457 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 2, 5, 2]
def baseStart_4943457 : Nat := 118140960795 + 4943457 * 2 ^ 59
def prefixEnd_4943457 : Nat := 4983230072969 + 3 ^ 40 * 4943457 * 2
def baseEnd_4943457 : Nat := 2538369535833370435452961

theorem tailTrace_4943457 : CollatzResearch.WordTrace tailWord_4943457 prefixEnd_4943457 2538369535833370435452961 := by
  unfold tailWord_4943457
  simp only [CollatzResearch.WordTrace]
  refine ⟨180302689251707039084524625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120201792834471359389683083 180302689251707039084524625)
  ·
    refine ⟨135227016938780279313393469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180302689251707039084524625 135227016938780279313393469)
    ·
      refine ⟨50710131352042604742522551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135227016938780279313393469 50710131352042604742522551)
      ·
        refine ⟨76065197028063907113783827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50710131352042604742522551 76065197028063907113783827)
        ·
          refine ⟨114097795542095860670675741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76065197028063907113783827 114097795542095860670675741)
          ·
            refine ⟨42786673328285947751503403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114097795542095860670675741 42786673328285947751503403)
            ·
              refine ⟨64180009992428921627255105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42786673328285947751503403 64180009992428921627255105)
              ·
                refine ⟨48135007494321691220441329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64180009992428921627255105 48135007494321691220441329)
                ·
                  refine ⟨36101255620741268415330997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48135007494321691220441329 36101255620741268415330997)
                  ·
                    refine ⟨3384492714444493913937281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36101255620741268415330997 3384492714444493913937281)
                    ·
                      refine ⟨2538369535833370435452961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3384492714444493913937281 2538369535833370435452961)
                      ·
                        rfl

theorem cell23_4943457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_4943457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943457 prefixEnd_4943457 := by exact prefixLift 4943457
  have htrace : WordTrace (prefixWord ++ tailWord_4943457) baseStart_4943457 baseEnd_4943457 := by
    simpa [prefixWord, tailWord_4943457, baseEnd_4943457] using wordTrace_append hprefix tailTrace_4943457
  have hstable : (prefixWord ++ tailWord_4943457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943457).length < 2 ^ (prefixWord ++ tailWord_4943457).sum := by decide
  have hdescent : baseEnd_4943457 < baseStart_4943457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943497 : List Nat := [1, 2, 1, 1, 4, 1, 3, 3, 3, 4]
def baseStart_4943497 : Nat := 118140960795 + 4943497 * 2 ^ 59
def prefixEnd_4943497 : Nat := 4983230072969 + 3 ^ 40 * 4943497 * 2
def baseEnd_4943497 : Nat := 846130025019850092984259

theorem tailTrace_4943497 : CollatzResearch.WordTrace tailWord_4943497 prefixEnd_4943497 846130025019850092984259 := by
  unfold tailWord_4943497
  simp only [CollatzResearch.WordTrace]
  refine ⟨180304148171562125915980745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120202765447708083943987163 180304148171562125915980745)
  ·
    refine ⟨135228111128671594436985559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180304148171562125915980745 135228111128671594436985559)
    ·
      refine ⟨202842166693007391655478339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135228111128671594436985559 202842166693007391655478339)
      ·
        refine ⟨304263250039511087483217509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202842166693007391655478339 304263250039511087483217509)
        ·
          refine ⟨57049359382408328903103283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 304263250039511087483217509 57049359382408328903103283)
          ·
            refine ⟨85574039073612493354654925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57049359382408328903103283 85574039073612493354654925)
            ·
              refine ⟨32090264652604685007995597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85574039073612493354654925 32090264652604685007995597)
              ·
                refine ⟨12033849244726756877998349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32090264652604685007995597 12033849244726756877998349)
                ·
                  refine ⟨4512693466772533829249381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12033849244726756877998349 4512693466772533829249381)
                  ·
                    refine ⟨846130025019850092984259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4512693466772533829249381 846130025019850092984259)
                    ·
                      rfl

theorem cell23_4943497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 4].length) (baseStart_4943497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943497 prefixEnd_4943497 := by exact prefixLift 4943497
  have htrace : WordTrace (prefixWord ++ tailWord_4943497) baseStart_4943497 baseEnd_4943497 := by
    simpa [prefixWord, tailWord_4943497, baseEnd_4943497] using wordTrace_append hprefix tailTrace_4943497
  have hstable : (prefixWord ++ tailWord_4943497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943497).length < 2 ^ (prefixWord ++ tailWord_4943497).sum := by decide
  have hdescent : baseEnd_4943497 < baseStart_4943497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943500 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 6]
def baseStart_4943500 : Nat := 118140960795 + 4943500 * 2 ^ 59
def prefixEnd_4943500 : Nat := 4983230072969 + 3 ^ 40 * 4943500 * 2
def baseEnd_4943500 : Nat := 2538391615501513767215263

theorem tailTrace_4943500 : CollatzResearch.WordTrace tailWord_4943500 prefixEnd_4943500 2538391615501513767215263 := by
  unfold tailWord_4943500
  simp only [CollatzResearch.WordTrace]
  refine ⟨90152128795275628714169977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120202838393700838285559969 90152128795275628714169977)
  ·
    refine ⟨67614096596456721535627483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90152128795275628714169977 67614096596456721535627483)
    ·
      refine ⟨101421144894685082303441225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67614096596456721535627483 101421144894685082303441225)
      ·
        refine ⟨76065858671013811727580919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101421144894685082303441225 76065858671013811727580919)
        ·
          refine ⟨114098788006520717591371379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76065858671013811727580919 114098788006520717591371379)
          ·
            refine ⟨171148182009781076387057069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114098788006520717591371379 171148182009781076387057069)
            ·
              refine ⟨64180568253667903645146401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171148182009781076387057069 64180568253667903645146401)
              ·
                refine ⟨48135426190250927733859801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64180568253667903645146401 48135426190250927733859801)
                ·
                  refine ⟨36101569642688195800394851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48135426190250927733859801 36101569642688195800394851)
                  ·
                    refine ⟨54152354464032293700592277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36101569642688195800394851 54152354464032293700592277)
                    ·
                      refine ⟨2538391615501513767215263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54152354464032293700592277 2538391615501513767215263)
                      ·
                        rfl

theorem cell23_4943500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_4943500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943500 prefixEnd_4943500 := by exact prefixLift 4943500
  have htrace : WordTrace (prefixWord ++ tailWord_4943500) baseStart_4943500 baseEnd_4943500 := by
    simpa [prefixWord, tailWord_4943500, baseEnd_4943500] using wordTrace_append hprefix tailTrace_4943500
  have hstable : (prefixWord ++ tailWord_4943500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943500).length < 2 ^ (prefixWord ++ tailWord_4943500).sum := by decide
  have hdescent : baseEnd_4943500 < baseStart_4943500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943541 : List Nat := [1, 3, 3, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_4943541 : Nat := 118140960795 + 4943541 * 2 ^ 59
def prefixEnd_4943541 : Nat := 4983230072969 + 3 ^ 40 * 4943541 * 2
def baseEnd_4943541 : Nat := 2538412668208348106802575

theorem tailTrace_4943541 : CollatzResearch.WordTrace tailWord_4943541 prefixEnd_4943541 2538412668208348106802575 := by
  unfold tailWord_4943541
  simp only [CollatzResearch.WordTrace]
  refine ⟨180305752983402721430582477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120203835322268480953721651 180305752983402721430582477)
  ·
    refine ⟨67614657368776020536468429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180305752983402721430582477 67614657368776020536468429)
    ·
      refine ⟨25355496513291007701175661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67614657368776020536468429 25355496513291007701175661)
      ·
        refine ⟨9508311192484127887940873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25355496513291007701175661 9508311192484127887940873)
        ·
          refine ⟨7131233394363095915955655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9508311192484127887940873 7131233394363095915955655)
          ·
            refine ⟨10696850091544643873933483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7131233394363095915955655 10696850091544643873933483)
            ·
              refine ⟨16045275137316965810900225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10696850091544643873933483 16045275137316965810900225)
              ·
                refine ⟨12033956352987724358175169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16045275137316965810900225 12033956352987724358175169)
                ·
                  refine ⟨9025467264740793268631377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12033956352987724358175169 9025467264740793268631377)
                  ·
                    refine ⟨6769100448555594951473533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9025467264740793268631377 6769100448555594951473533)
                    ·
                      refine ⟨2538412668208348106802575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6769100448555594951473533 2538412668208348106802575)
                      ·
                        rfl

theorem cell23_4943541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_4943541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943541 prefixEnd_4943541 := by exact prefixLift 4943541
  have htrace : WordTrace (prefixWord ++ tailWord_4943541) baseStart_4943541 baseEnd_4943541 := by
    simpa [prefixWord, tailWord_4943541, baseEnd_4943541] using wordTrace_append hprefix tailTrace_4943541
  have hstable : (prefixWord ++ tailWord_4943541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943541).length < 2 ^ (prefixWord ++ tailWord_4943541).sum := by decide
  have hdescent : baseEnd_4943541 < baseStart_4943541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943548 : List Nat := [2, 2, 2, 3, 1, 3, 3, 2, 1, 4]
def baseStart_4943548 : Nat := 118140960795 + 4943548 * 2 ^ 59
def prefixEnd_4943548 : Nat := 4983230072969 + 3 ^ 40 * 4943548 * 2
def baseEnd_4943548 : Nat := 846138754190976526471681

theorem tailTrace_4943548 : CollatzResearch.WordTrace tailWord_4943548 prefixEnd_4943548 846138754190976526471681 := by
  unfold tailWord_4943548
  simp only [CollatzResearch.WordTrace]
  refine ⟨90153004147188680813043649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120204005529584907750724865 90153004147188680813043649)
  ·
    refine ⟨67614753110391510609782737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90153004147188680813043649 67614753110391510609782737)
    ·
      refine ⟨50711064832793632957337053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67614753110391510609782737 50711064832793632957337053)
      ·
        refine ⟨19016649312297612359001395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50711064832793632957337053 19016649312297612359001395)
        ·
          refine ⟨28524973968446418538502093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19016649312297612359001395 28524973968446418538502093)
          ·
            refine ⟨10696865238167406951938285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28524973968446418538502093 10696865238167406951938285)
            ·
              refine ⟨4011324464312777606976857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10696865238167406951938285 4011324464312777606976857)
              ·
                refine ⟨3008493348234583205232643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4011324464312777606976857 3008493348234583205232643)
                ·
                  refine ⟨4512740022351874807848965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3008493348234583205232643 4512740022351874807848965)
                  ·
                    refine ⟨846138754190976526471681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4512740022351874807848965 846138754190976526471681)
                    ·
                      rfl

theorem cell23_4943548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_4943548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943548 prefixEnd_4943548 := by exact prefixLift 4943548
  have htrace : WordTrace (prefixWord ++ tailWord_4943548) baseStart_4943548 baseEnd_4943548 := by
    simpa [prefixWord, tailWord_4943548, baseEnd_4943548] using wordTrace_append hprefix tailTrace_4943548
  have hstable : (prefixWord ++ tailWord_4943548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943548).length < 2 ^ (prefixWord ++ tailWord_4943548).sum := by decide
  have hdescent : baseEnd_4943548 < baseStart_4943548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943594 : List Nat := [3, 1, 3, 1, 1, 1, 2, 5, 1, 1, 4]
def baseStart_4943594 : Nat := 118140960795 + 4943594 * 2 ^ 59
def prefixEnd_4943594 : Nat := 4983230072969 + 3 ^ 40 * 4943594 * 2
def baseEnd_4943594 : Nat := 2538439882683036399439831

theorem tailTrace_4943594 : CollatzResearch.WordTrace tailWord_4943594 prefixEnd_4943594 2538439882683036399439831 := by
  unfold tailWord_4943594
  simp only [CollatzResearch.WordTrace]
  refine ⟨45076921513052677870565459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120205124034807140988174557 45076921513052677870565459)
  ·
    refine ⟨67615382269579016805848189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45076921513052677870565459 67615382269579016805848189)
    ·
      refine ⟨25355768351092131302193071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67615382269579016805848189 25355768351092131302193071)
      ·
        refine ⟨38033652526638196953289607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25355768351092131302193071 38033652526638196953289607)
        ·
          refine ⟨57050478789957295429934411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38033652526638196953289607 57050478789957295429934411)
          ·
            refine ⟨85575718184935943144901617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57050478789957295429934411 85575718184935943144901617)
            ·
              refine ⟨64181788638701957358676213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85575718184935943144901617 64181788638701957358676213)
              ·
                refine ⟨6017042684878308502375895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64181788638701957358676213 6017042684878308502375895)
                ·
                  refine ⟨9025564027317462753563843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6017042684878308502375895 9025564027317462753563843)
                  ·
                    refine ⟨13538346040976194130345765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9025564027317462753563843 13538346040976194130345765)
                    ·
                      refine ⟨2538439882683036399439831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13538346040976194130345765 2538439882683036399439831)
                      ·
                        rfl

theorem cell23_4943594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_4943594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943594 prefixEnd_4943594 := by exact prefixLift 4943594
  have htrace : WordTrace (prefixWord ++ tailWord_4943594) baseStart_4943594 baseEnd_4943594 := by
    simpa [prefixWord, tailWord_4943594, baseEnd_4943594] using wordTrace_append hprefix tailTrace_4943594
  have hstable : (prefixWord ++ tailWord_4943594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943594).length < 2 ^ (prefixWord ++ tailWord_4943594).sum := by decide
  have hdescent : baseEnd_4943594 < baseStart_4943594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943617 : List Nat := [1, 2, 4, 1, 1, 1, 5, 8]
def baseStart_4943617 : Nat := 118140960795 + 4943617 * 2 ^ 59
def prefixEnd_4943617 : Nat := 4983230072969 + 3 ^ 40 * 4943617 * 2
def baseEnd_4943617 : Nat := 94016729360669992942675

theorem tailTrace_4943617 : CollatzResearch.WordTrace tailWord_4943617 prefixEnd_4943617 94016729360669992942675 := by
  unfold tailWord_4943617
  simp only [CollatzResearch.WordTrace]
  refine ⟨180308524931127386410349105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120205683287418257606899403 180308524931127386410349105)
  ·
    refine ⟨135231393698345539807761829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180308524931127386410349105 135231393698345539807761829)
    ·
      refine ⟨25355886318439788713955343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135231393698345539807761829 25355886318439788713955343)
      ·
        refine ⟨38033829477659683070933015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25355886318439788713955343 38033829477659683070933015)
        ·
          refine ⟨57050744216489524606399523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38033829477659683070933015 57050744216489524606399523)
          ·
            refine ⟨85576116324734286909599285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57050744216489524606399523 85576116324734286909599285)
            ·
              refine ⟨8022760905443839397774933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85576116324734286909599285 8022760905443839397774933)
              ·
                refine ⟨94016729360669992942675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8022760905443839397774933 94016729360669992942675)
                ·
                  rfl

theorem cell23_4943617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 8].length) (baseStart_4943617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943617 prefixEnd_4943617 := by exact prefixLift 4943617
  have htrace : WordTrace (prefixWord ++ tailWord_4943617) baseStart_4943617 baseEnd_4943617 := by
    simpa [prefixWord, tailWord_4943617, baseEnd_4943617] using wordTrace_append hprefix tailTrace_4943617
  have hstable : (prefixWord ++ tailWord_4943617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943617).length < 2 ^ (prefixWord ++ tailWord_4943617).sum := by decide
  have hdescent : baseEnd_4943617 < baseStart_4943617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943624 : List Nat := [2, 1, 3, 2, 2, 1, 4, 1, 1, 2, 4]
def baseStart_4943624 : Nat := 118140960795 + 4943624 * 2 ^ 59
def prefixEnd_4943624 : Nat := 4983230072969 + 3 ^ 40 * 4943624 * 2
def baseEnd_4943624 : Nat := 2538455287102671282064693

theorem tailTrace_4943624 : CollatzResearch.WordTrace tailWord_4943624 prefixEnd_4943624 2538455287102671282064693 := by
  unfold tailWord_4943624
  simp only [CollatzResearch.WordTrace]
  refine ⟨90154390121051013302926963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120205853494734684403902617 90154390121051013302926963)
  ·
    refine ⟨135231585181576519954390445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90154390121051013302926963 135231585181576519954390445)
    ·
      refine ⟨50711844443091194982896417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135231585181576519954390445 50711844443091194982896417)
      ·
        refine ⟨38033883332318396237172313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50711844443091194982896417 38033883332318396237172313)
        ·
          refine ⟨28525412499238797177879235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38033883332318396237172313 28525412499238797177879235)
          ·
            refine ⟨42788118748858195766818853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28525412499238797177879235 42788118748858195766818853)
            ·
              refine ⟨8022772265410911706278535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42788118748858195766818853 8022772265410911706278535)
              ·
                refine ⟨12034158398116367559417803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8022772265410911706278535 12034158398116367559417803)
                ·
                  refine ⟨18051237597174551339126705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12034158398116367559417803 18051237597174551339126705)
                  ·
                    refine ⟨13538428197880913504345029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18051237597174551339126705 13538428197880913504345029)
                    ·
                      refine ⟨2538455287102671282064693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13538428197880913504345029 2538455287102671282064693)
                      ·
                        rfl

theorem cell23_4943624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_4943624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943624 prefixEnd_4943624 := by exact prefixLift 4943624
  have htrace : WordTrace (prefixWord ++ tailWord_4943624) baseStart_4943624 baseEnd_4943624 := by
    simpa [prefixWord, tailWord_4943624, baseEnd_4943624] using wordTrace_append hprefix tailTrace_4943624
  have hstable : (prefixWord ++ tailWord_4943624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943624).length < 2 ^ (prefixWord ++ tailWord_4943624).sum := by decide
  have hdescent : baseEnd_4943624 < baseStart_4943624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943644 : List Nat := [2, 2, 3, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_4943644 : Nat := 118140960795 + 4943644 * 2 ^ 59
def prefixEnd_4943644 : Nat := 4983230072969 + 3 ^ 40 * 4943644 * 2
def baseEnd_4943644 : Nat := 2538465556715761203814601

theorem tailTrace_4943644 : CollatzResearch.WordTrace tailWord_4943644 prefixEnd_4943644 2538465556715761203814601 := by
  unfold tailWord_4943644
  simp only [CollatzResearch.WordTrace]
  refine ⟨90154754851014785010790993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120206339801353046681054657 90154754851014785010790993)
  ·
    refine ⟨67616066138261088758093245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90154754851014785010790993 67616066138261088758093245)
    ·
      refine ⟨25356024801847908284284967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67616066138261088758093245 25356024801847908284284967)
      ·
        refine ⟨38034037202771862426427451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25356024801847908284284967 38034037202771862426427451)
        ·
          refine ⟨57051055804157793639641177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38034037202771862426427451 57051055804157793639641177)
          ·
            refine ⟨42788291853118345229730883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57051055804157793639641177 42788291853118345229730883)
            ·
              refine ⟨64182437779677517844596325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42788291853118345229730883 64182437779677517844596325)
              ·
                refine ⟨12034207083689534595861811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64182437779677517844596325 12034207083689534595861811)
                ·
                  refine ⟨18051310625534301893792717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12034207083689534595861811 18051310625534301893792717)
                  ·
                    refine ⟨6769241484575363210172269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18051310625534301893792717 6769241484575363210172269)
                    ·
                      refine ⟨2538465556715761203814601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6769241484575363210172269 2538465556715761203814601)
                      ·
                        rfl

theorem cell23_4943644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_4943644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943644 prefixEnd_4943644 := by exact prefixLift 4943644
  have htrace : WordTrace (prefixWord ++ tailWord_4943644) baseStart_4943644 baseEnd_4943644 := by
    simpa [prefixWord, tailWord_4943644, baseEnd_4943644] using wordTrace_append hprefix tailTrace_4943644
  have hstable : (prefixWord ++ tailWord_4943644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943644).length < 2 ^ (prefixWord ++ tailWord_4943644).sum := by decide
  have hdescent : baseEnd_4943644 < baseStart_4943644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943678 : List Nat := [4, 2, 1, 2, 2, 3, 1, 1, 1, 3, 3]
def baseStart_4943678 : Nat := 118140960795 + 4943678 * 2 ^ 59
def prefixEnd_4943678 : Nat := 4983230072969 + 3 ^ 40 * 4943678 * 2
def baseEnd_4943678 : Nat := 2538483015058014070789445

theorem tailTrace_4943678 : CollatzResearch.WordTrace tailWord_4943678 prefixEnd_4943678 2538483015058014070789445 := by
  unfold tailWord_4943678
  simp only [CollatzResearch.WordTrace]
  refine ⟨22538843722988299228539961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120207166522604262552213125 22538843722988299228539961)
  ·
    refine ⟨16904132792241224421404971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22538843722988299228539961 16904132792241224421404971)
    ·
      refine ⟨25356199188361836632107457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16904132792241224421404971 25356199188361836632107457)
      ·
        refine ⟨19017149391271377474080593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25356199188361836632107457 19017149391271377474080593)
        ·
          refine ⟨14262862043453533105560445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19017149391271377474080593 14262862043453533105560445)
          ·
            refine ⟨5348573266295074914585167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14262862043453533105560445 5348573266295074914585167)
            ·
              refine ⟨8022859899442612371877751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5348573266295074914585167 8022859899442612371877751)
              ·
                refine ⟨12034289849163918557816627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8022859899442612371877751 12034289849163918557816627)
                ·
                  refine ⟨18051434773745877836724941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12034289849163918557816627 18051434773745877836724941)
                  ·
                    refine ⟨6769288040154704188771853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18051434773745877836724941 6769288040154704188771853)
                    ·
                      refine ⟨2538483015058014070789445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6769288040154704188771853 2538483015058014070789445)
                      ·
                        rfl

theorem cell23_4943678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_4943678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943678 prefixEnd_4943678 := by exact prefixLift 4943678
  have htrace : WordTrace (prefixWord ++ tailWord_4943678) baseStart_4943678 baseEnd_4943678 := by
    simpa [prefixWord, tailWord_4943678, baseEnd_4943678] using wordTrace_append hprefix tailTrace_4943678
  have hstable : (prefixWord ++ tailWord_4943678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943678).length < 2 ^ (prefixWord ++ tailWord_4943678).sum := by decide
  have hdescent : baseEnd_4943678 < baseStart_4943678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943688 : List Nat := [2, 1, 3, 1, 1, 5, 2, 2, 1, 3, 2]
def baseStart_4943688 : Nat := 118140960795 + 4943688 * 2 ^ 59
def prefixEnd_4943688 : Nat := 4983230072969 + 3 ^ 40 * 4943688 * 2
def baseEnd_4943688 : Nat := 2538488149864559031664399

theorem tailTrace_4943688 : CollatzResearch.WordTrace tailWord_4943688 prefixEnd_4943688 2538488149864559031664399 := by
  unfold tailWord_4943688
  simp only [CollatzResearch.WordTrace]
  refine ⟨90155557256935082768091859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120207409675913443690789145 90155557256935082768091859)
  ·
    refine ⟨135233335885402624152137789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90155557256935082768091859 135233335885402624152137789)
    ·
      refine ⟨50712500957025984057051671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135233335885402624152137789 50712500957025984057051671)
      ·
        refine ⟨76068751435538976085577507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50712500957025984057051671 76068751435538976085577507)
        ·
          refine ⟨114103127153308464128366261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76068751435538976085577507 114103127153308464128366261)
          ·
            refine ⟨10697168170622668512034337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114103127153308464128366261 10697168170622668512034337)
            ·
              refine ⟨8022876127967001384025753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10697168170622668512034337 8022876127967001384025753)
              ·
                refine ⟨6017157095975251038019315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8022876127967001384025753 6017157095975251038019315)
                ·
                  refine ⟨9025735643962876557028973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6017157095975251038019315 9025735643962876557028973)
                  ·
                    refine ⟨3384650866486078708885865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9025735643962876557028973 3384650866486078708885865)
                    ·
                      refine ⟨2538488149864559031664399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3384650866486078708885865 2538488149864559031664399)
                      ·
                        rfl

theorem cell23_4943688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_4943688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943688 prefixEnd_4943688 := by exact prefixLift 4943688
  have htrace : WordTrace (prefixWord ++ tailWord_4943688) baseStart_4943688 baseEnd_4943688 := by
    simpa [prefixWord, tailWord_4943688, baseEnd_4943688] using wordTrace_append hprefix tailTrace_4943688
  have hstable : (prefixWord ++ tailWord_4943688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943688).length < 2 ^ (prefixWord ++ tailWord_4943688).sum := by decide
  have hdescent : baseEnd_4943688 < baseStart_4943688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943717 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 9]
def baseStart_4943717 : Nat := 118140960795 + 4943717 * 2 ^ 59
def prefixEnd_4943717 : Nat := 4983230072969 + 3 ^ 40 * 4943717 * 2
def baseEnd_4943717 : Nat := 2538503040803539418201765

theorem tailTrace_4943717 : CollatzResearch.WordTrace tailWord_4943717 prefixEnd_4943717 2538503040803539418201765 := by
  unfold tailWord_4943717
  simp only [CollatzResearch.WordTrace]
  refine ⟨180312172230765103488989405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120208114820510068992659603 180312172230765103488989405)
  ·
    refine ⟨67617064586536913808371027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180312172230765103488989405 67617064586536913808371027)
    ·
      refine ⟨101425596879805370712556541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67617064586536913808371027 101425596879805370712556541)
      ·
        refine ⟨38034598829927014017208703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101425596879805370712556541 38034598829927014017208703)
        ·
          refine ⟨57051898244890521025813055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38034598829927014017208703 57051898244890521025813055)
          ·
            refine ⟨85577847367335781538719583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57051898244890521025813055 85577847367335781538719583)
            ·
              refine ⟨128366771051003672308079375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85577847367335781538719583 128366771051003672308079375)
              ·
                refine ⟨192550156576505508462119063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128366771051003672308079375 192550156576505508462119063)
                ·
                  refine ⟨288825234864758262693178595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192550156576505508462119063 288825234864758262693178595)
                  ·
                    refine ⟨433237852297137394039767893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 288825234864758262693178595 433237852297137394039767893)
                    ·
                      refine ⟨2538503040803539418201765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 433237852297137394039767893 2538503040803539418201765)
                      ·
                        rfl

theorem cell23_4943717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_4943717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943717 prefixEnd_4943717 := by exact prefixLift 4943717
  have htrace : WordTrace (prefixWord ++ tailWord_4943717) baseStart_4943717 baseEnd_4943717 := by
    simpa [prefixWord, tailWord_4943717, baseEnd_4943717] using wordTrace_append hprefix tailTrace_4943717
  have hstable : (prefixWord ++ tailWord_4943717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943717).length < 2 ^ (prefixWord ++ tailWord_4943717).sum := by decide
  have hdescent : baseEnd_4943717 < baseStart_4943717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943724 : List Nat := [2, 2, 1, 1, 4, 2, 3, 1, 7]
def baseStart_4943724 : Nat := 118140960795 + 4943724 * 2 ^ 59
def prefixEnd_4943724 : Nat := 4983230072969 + 3 ^ 40 * 4943724 * 2
def baseEnd_4943724 : Nat := 282056292796457876757137

theorem tailTrace_4943724 : CollatzResearch.WordTrace tailWord_4943724 prefixEnd_4943724 282056292796457876757137 := by
  unfold tailWord_4943724
  simp only [CollatzResearch.WordTrace]
  refine ⟨90156213770869871842247113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120208285027826495789662817 90156213770869871842247113)
  ·
    refine ⟨67617160328152403881685335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90156213770869871842247113 67617160328152403881685335)
    ·
      refine ⟨101425740492228605822528003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67617160328152403881685335 101425740492228605822528003)
      ·
        refine ⟨152138610738342908733792005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101425740492228605822528003 152138610738342908733792005)
        ·
          refine ⟨28525989513439295387586001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152138610738342908733792005 28525989513439295387586001)
          ·
            refine ⟨21394492135079471540689501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28525989513439295387586001 21394492135079471540689501)
            ·
              refine ⟨8022934550654801827758563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21394492135079471540689501 8022934550654801827758563)
              ·
                refine ⟨12034401825982202741637845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8022934550654801827758563 12034401825982202741637845)
                ·
                  refine ⟨282056292796457876757137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12034401825982202741637845 282056292796457876757137)
                  ·
                    rfl

theorem cell23_4943724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 7].length) (baseStart_4943724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943724 prefixEnd_4943724 := by exact prefixLift 4943724
  have htrace : WordTrace (prefixWord ++ tailWord_4943724) baseStart_4943724 baseEnd_4943724 := by
    simpa [prefixWord, tailWord_4943724, baseEnd_4943724] using wordTrace_append hprefix tailTrace_4943724
  have hstable : (prefixWord ++ tailWord_4943724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943724).length < 2 ^ (prefixWord ++ tailWord_4943724).sum := by decide
  have hdescent : baseEnd_4943724 < baseStart_4943724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943775 : List Nat := [1, 1, 2, 5, 3, 2, 2, 2, 5]
def baseStart_4943775 : Nat := 118140960795 + 4943775 * 2 ^ 59
def prefixEnd_4943775 : Nat := 4983230072969 + 3 ^ 40 * 4943775 * 2
def baseEnd_4943775 : Nat := 282059202520166687919611

theorem tailTrace_4943775 : CollatzResearch.WordTrace tailWord_4943775 prefixEnd_4943775 282059202520166687919611 := by
  unfold tailWord_4943775
  simp only [CollatzResearch.WordTrace]
  refine ⟨180314287664554979394600779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120209525109703319596400519 180314287664554979394600779)
  ·
    refine ⟨270471431496832469091901169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180314287664554979394600779 270471431496832469091901169)
    ·
      refine ⟨202853573622624351818925877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270471431496832469091901169 202853573622624351818925877)
      ·
        refine ⟨19017522527121032983024301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 202853573622624351818925877 19017522527121032983024301)
        ·
          refine ⟨7131570947670387368634113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19017522527121032983024301 7131570947670387368634113)
          ·
            refine ⟨5348678210752790526475585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7131570947670387368634113 5348678210752790526475585)
            ·
              refine ⟨4011508658064592894856689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5348678210752790526475585 4011508658064592894856689)
              ·
                refine ⟨3008631493548444671142517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4011508658064592894856689 3008631493548444671142517)
                ·
                  refine ⟨282059202520166687919611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3008631493548444671142517 282059202520166687919611)
                  ·
                    rfl

theorem cell23_4943775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 5].length) (baseStart_4943775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943775 prefixEnd_4943775 := by exact prefixLift 4943775
  have htrace : WordTrace (prefixWord ++ tailWord_4943775) baseStart_4943775 baseEnd_4943775 := by
    simpa [prefixWord, tailWord_4943775, baseEnd_4943775] using wordTrace_append hprefix tailTrace_4943775
  have hstable : (prefixWord ++ tailWord_4943775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943775).length < 2 ^ (prefixWord ++ tailWord_4943775).sum := by decide
  have hdescent : baseEnd_4943775 < baseStart_4943775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943791 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 2, 4, 2]
def baseStart_4943791 : Nat := 118140960795 + 4943791 * 2 ^ 59
def prefixEnd_4943791 : Nat := 4983230072969 + 3 ^ 40 * 4943791 * 2
def baseEnd_4943791 : Nat := 2538541038371972128676425

theorem tailTrace_4943791 : CollatzResearch.WordTrace tailWord_4943791 prefixEnd_4943791 2538541038371972128676425 := by
  unfold tailWord_4943791
  simp only [CollatzResearch.WordTrace]
  refine ⟨180314871232497014127183227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120209914154998009418122151 180314871232497014127183227)
  ·
    refine ⟨270472306848745521190774841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180314871232497014127183227 270472306848745521190774841)
    ·
      refine ⟨202854230136559140893081131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270472306848745521190774841 202854230136559140893081131)
      ·
        refine ⟨304281345204838711339621697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202854230136559140893081131 304281345204838711339621697)
        ·
          refine ⟨228211008903629033504716273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304281345204838711339621697 228211008903629033504716273)
          ·
            refine ⟨171158256677721775128537205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228211008903629033504716273 171158256677721775128537205)
            ·
              refine ⟨16046086563536416418300363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 171158256677721775128537205 16046086563536416418300363)
              ·
                refine ⟨24069129845304624627450545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16046086563536416418300363 24069129845304624627450545)
                ·
                  refine ⟨18051847383978468470587909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24069129845304624627450545 18051847383978468470587909)
                  ·
                    refine ⟨3384721384495962838235233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18051847383978468470587909 3384721384495962838235233)
                    ·
                      refine ⟨2538541038371972128676425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3384721384495962838235233 2538541038371972128676425)
                      ·
                        rfl

theorem cell23_4943791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 4, 2].length) (baseStart_4943791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943791 prefixEnd_4943791 := by exact prefixLift 4943791
  have htrace : WordTrace (prefixWord ++ tailWord_4943791) baseStart_4943791 baseEnd_4943791 := by
    simpa [prefixWord, tailWord_4943791, baseEnd_4943791] using wordTrace_append hprefix tailTrace_4943791
  have hstable : (prefixWord ++ tailWord_4943791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943791).length < 2 ^ (prefixWord ++ tailWord_4943791).sum := by decide
  have hdescent : baseEnd_4943791 < baseStart_4943791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943801 : List Nat := [1, 2, 1, 4, 2, 1, 3, 2, 3, 4]
def baseStart_4943801 : Nat := 118140960795 + 4943801 * 2 ^ 59
def prefixEnd_4943801 : Nat := 4983230072969 + 3 ^ 40 * 4943801 * 2
def baseEnd_4943801 : Nat := 846182057726172363183793

theorem tailTrace_4943801 : CollatzResearch.WordTrace tailWord_4943801 prefixEnd_4943801 846182057726172363183793 := by
  unfold tailWord_4943801
  simp only [CollatzResearch.WordTrace]
  refine ⟨180315235962460785835047257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120210157308307190556698171 180315235962460785835047257)
  ·
    refine ⟨135236426971845589376285443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180315235962460785835047257 135236426971845589376285443)
    ·
      refine ⟨202854640457768384064428165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135236426971845589376285443 202854640457768384064428165)
      ·
        refine ⟨38035245085831572012080281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 202854640457768384064428165 38035245085831572012080281)
        ·
          refine ⟨28526433814373679009060211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38035245085831572012080281 28526433814373679009060211)
          ·
            refine ⟨42789650721560518513590317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28526433814373679009060211 42789650721560518513590317)
            ·
              refine ⟨16046119020585194442596369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42789650721560518513590317 16046119020585194442596369)
              ·
                refine ⟨12034589265438895831947277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16046119020585194442596369 12034589265438895831947277)
                ·
                  refine ⟨4512970974539585936980229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12034589265438895831947277 4512970974539585936980229)
                  ·
                    refine ⟨846182057726172363183793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4512970974539585936980229 846182057726172363183793)
                    ·
                      rfl

theorem cell23_4943801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 4].length) (baseStart_4943801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943801 prefixEnd_4943801 := by exact prefixLift 4943801
  have htrace : WordTrace (prefixWord ++ tailWord_4943801) baseStart_4943801 baseEnd_4943801 := by
    simpa [prefixWord, tailWord_4943801, baseEnd_4943801] using wordTrace_append hprefix tailTrace_4943801
  have hstable : (prefixWord ++ tailWord_4943801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943801).length < 2 ^ (prefixWord ++ tailWord_4943801).sum := by decide
  have hdescent : baseEnd_4943801 < baseStart_4943801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943818 : List Nat := [3, 1, 2, 1, 2, 1, 3, 5, 1, 4]
def baseStart_4943818 : Nat := 118140960795 + 4943818 * 2 ^ 59
def prefixEnd_4943818 : Nat := 4983230072969 + 3 ^ 40 * 4943818 * 2
def baseEnd_4943818 : Nat := 846184967449881174346267

theorem tailTrace_4943818 : CollatzResearch.WordTrace tailWord_4943818 prefixEnd_4943818 846184967449881174346267 := by
  unfold tailWord_4943818
  simp only [CollatzResearch.WordTrace]
  refine ⟨45078964000849799434604027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120210570668932798492277405 45078964000849799434604027)
  ·
    refine ⟨67618446001274699151906041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45078964000849799434604027 67618446001274699151906041)
    ·
      refine ⟨50713834500956024363929531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67618446001274699151906041 50713834500956024363929531)
      ·
        refine ⟨76070751751434036545894297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50713834500956024363929531 76070751751434036545894297)
        ·
          refine ⟨57053063813575527409420723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76070751751434036545894297 57053063813575527409420723)
          ·
            refine ⟨85579595720363291114131085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57053063813575527409420723 85579595720363291114131085)
            ·
              refine ⟨32092348395136234167799157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85579595720363291114131085 32092348395136234167799157)
              ·
                refine ⟨3008657662044021953231171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32092348395136234167799157 3008657662044021953231171)
                ·
                  refine ⟨4512986493066032929846757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3008657662044021953231171 4512986493066032929846757)
                  ·
                    refine ⟨846184967449881174346267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4512986493066032929846757 846184967449881174346267)
                    ·
                      rfl

theorem cell23_4943818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_4943818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943818 prefixEnd_4943818 := by exact prefixLift 4943818
  have htrace : WordTrace (prefixWord ++ tailWord_4943818) baseStart_4943818 baseEnd_4943818 := by
    simpa [prefixWord, tailWord_4943818, baseEnd_4943818] using wordTrace_append hprefix tailTrace_4943818
  have hstable : (prefixWord ++ tailWord_4943818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943818).length < 2 ^ (prefixWord ++ tailWord_4943818).sum := by decide
  have hdescent : baseEnd_4943818 < baseStart_4943818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943868 : List Nat := [2, 2, 2, 1, 2, 2, 2, 3, 2, 3, 2]
def baseStart_4943868 : Nat := 118140960795 + 4943868 * 2 ^ 59
def prefixEnd_4943868 : Nat := 4983230072969 + 3 ^ 40 * 4943868 * 2
def baseEnd_4943868 : Nat := 2538580576382368327413571

theorem tailTrace_4943868 : CollatzResearch.WordTrace tailWord_4943868 prefixEnd_4943868 2538580576382368327413571 := by
  unfold tailWord_4943868
  simp only [CollatzResearch.WordTrace]
  refine ⟨90158839826609028138868129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120211786435478704185157505 90158839826609028138868129)
  ·
    refine ⟨67619129869956771104151097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90158839826609028138868129 67619129869956771104151097)
    ·
      refine ⟨50714347402467578328113323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67619129869956771104151097 50714347402467578328113323)
      ·
        refine ⟨76071521103701367492169985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50714347402467578328113323 76071521103701367492169985)
        ·
          refine ⟨57053640827776025619127489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76071521103701367492169985 57053640827776025619127489)
          ·
            refine ⟨42790230620832019214345617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57053640827776025619127489 42790230620832019214345617)
            ·
              refine ⟨32092672965624014410759213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42790230620832019214345617 32092672965624014410759213)
              ·
                refine ⟨12034752362109005404034705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32092672965624014410759213 12034752362109005404034705)
                ·
                  refine ⟨9026064271581754053026029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12034752362109005404034705 9026064271581754053026029)
                  ·
                    refine ⟨3384774101843157769884761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9026064271581754053026029 3384774101843157769884761)
                    ·
                      refine ⟨2538580576382368327413571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3384774101843157769884761 2538580576382368327413571)
                      ·
                        rfl

theorem cell23_4943868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_4943868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943868 prefixEnd_4943868 := by exact prefixLift 4943868
  have htrace : WordTrace (prefixWord ++ tailWord_4943868) baseStart_4943868 baseEnd_4943868 := by
    simpa [prefixWord, tailWord_4943868, baseEnd_4943868] using wordTrace_append hprefix tailTrace_4943868
  have hstable : (prefixWord ++ tailWord_4943868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943868).length < 2 ^ (prefixWord ++ tailWord_4943868).sum := by decide
  have hdescent : baseEnd_4943868 < baseStart_4943868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943891 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 4, 4]
def baseStart_4943891 : Nat := 118140960795 + 4943891 * 2 ^ 59
def prefixEnd_4943891 : Nat := 4983230072969 + 3 ^ 40 * 4943891 * 2
def baseEnd_4943891 : Nat := 846197462145807245808655

theorem tailTrace_4943891 : CollatzResearch.WordTrace tailWord_4943891 prefixEnd_4943891 846197462145807245808655 := by
  unfold tailWord_4943891
  simp only [CollatzResearch.WordTrace]
  refine ⟨180318518532134731205823527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120212345688089820803882351 180318518532134731205823527)
  ·
    refine ⟨270477777798202096808735291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180318518532134731205823527 270477777798202096808735291)
    ·
      refine ⟨405716666697303145213102937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270477777798202096808735291 405716666697303145213102937)
      ·
        refine ⟨304287500022977358909827203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 405716666697303145213102937 304287500022977358909827203)
        ·
          refine ⟨456431250034466038364740805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304287500022977358909827203 456431250034466038364740805)
          ·
            refine ⟨85580859381462382193388901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 456431250034466038364740805 85580859381462382193388901)
            ·
              refine ⟨16046411134024196661260419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85580859381462382193388901 16046411134024196661260419)
              ·
                refine ⟨24069616701036294991890629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16046411134024196661260419 24069616701036294991890629)
                ·
                  refine ⟨4513053131444305310979493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24069616701036294991890629 4513053131444305310979493)
                  ·
                    refine ⟨846197462145807245808655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4513053131444305310979493 846197462145807245808655)
                    ·
                      rfl

theorem cell23_4943891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 4].length) (baseStart_4943891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943891 prefixEnd_4943891 := by exact prefixLift 4943891
  have htrace : WordTrace (prefixWord ++ tailWord_4943891) baseStart_4943891 baseEnd_4943891 := by
    simpa [prefixWord, tailWord_4943891, baseEnd_4943891] using wordTrace_append hprefix tailTrace_4943891
  have hstable : (prefixWord ++ tailWord_4943891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943891).length < 2 ^ (prefixWord ++ tailWord_4943891).sum := by decide
  have hdescent : baseEnd_4943891 < baseStart_4943891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943912 : List Nat := [2, 1, 5, 3, 1, 2, 1, 2, 1, 5]
def baseStart_4943912 : Nat := 118140960795 + 4943912 * 2 ^ 59
def prefixEnd_4943912 : Nat := 4983230072969 + 3 ^ 40 * 4943912 * 2
def baseEnd_4943912 : Nat := 846201056510388718421123

theorem tailTrace_4943912 : CollatzResearch.WordTrace tailWord_4943912 prefixEnd_4943912 846201056510388718421123 := by
  unfold tailWord_4943912
  simp only [CollatzResearch.WordTrace]
  refine ⟨90159642232529325896168995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120212856310039101194891993 90159642232529325896168995)
  ·
    refine ⟨135239463348793988844253493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90159642232529325896168995 135239463348793988844253493)
    ·
      refine ⟨12678699688949436454148765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135239463348793988844253493 12678699688949436454148765)
      ·
        refine ⟨4754512383356038670305787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12678699688949436454148765 4754512383356038670305787)
        ·
          refine ⟨7131768575034058005458681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4754512383356038670305787 7131768575034058005458681)
          ·
            refine ⟨5348826431275543504094011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7131768575034058005458681 5348826431275543504094011)
            ·
              refine ⟨8023239646913315256141017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5348826431275543504094011 8023239646913315256141017)
              ·
                refine ⟨6017429735184986442105763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8023239646913315256141017 6017429735184986442105763)
                ·
                  refine ⟨9026144602777479663158645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6017429735184986442105763 9026144602777479663158645)
                  ·
                    refine ⟨846201056510388718421123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9026144602777479663158645 846201056510388718421123)
                    ·
                      rfl

theorem cell23_4943912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_4943912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943912 prefixEnd_4943912 := by exact prefixLift 4943912
  have htrace : WordTrace (prefixWord ++ tailWord_4943912) baseStart_4943912 baseEnd_4943912 := by
    simpa [prefixWord, tailWord_4943912, baseEnd_4943912] using wordTrace_append hprefix tailTrace_4943912
  have hstable : (prefixWord ++ tailWord_4943912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943912).length < 2 ^ (prefixWord ++ tailWord_4943912).sum := by decide
  have hdescent : baseEnd_4943912 < baseStart_4943912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943928 : List Nat := [2, 1, 2, 1, 6, 1, 1, 2, 1, 2, 4]
def baseStart_4943928 : Nat := 118140960795 + 4943928 * 2 ^ 59
def prefixEnd_4943928 : Nat := 4983230072969 + 3 ^ 40 * 4943928 * 2
def baseEnd_4943928 : Nat := 2538611385221638092663295

theorem tailTrace_4943928 : CollatzResearch.WordTrace tailWord_4943928 prefixEnd_4943928 2538611385221638092663295 := by
  unfold tailWord_4943928
  simp only [CollatzResearch.WordTrace]
  refine ⟨90159934016500343262460219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120213245355333791016613625 90159934016500343262460219)
  ·
    refine ⟨135239901024750514893690329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90159934016500343262460219 135239901024750514893690329)
    ·
      refine ⟨101429925768562886170267747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135239901024750514893690329 101429925768562886170267747)
      ·
        refine ⟨152144888652844329255401621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101429925768562886170267747 152144888652844329255401621)
        ·
          refine ⟨7131791655602077933846951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 152144888652844329255401621 7131791655602077933846951)
          ·
            refine ⟨10697687483403116900770427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7131791655602077933846951 10697687483403116900770427)
            ·
              refine ⟨16046531225104675351155641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10697687483403116900770427 16046531225104675351155641)
              ·
                refine ⟨12034898418828506513366731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16046531225104675351155641 12034898418828506513366731)
                ·
                  refine ⟨18052347628242759770050097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12034898418828506513366731 18052347628242759770050097)
                  ·
                    refine ⟨13539260721182069827537573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18052347628242759770050097 13539260721182069827537573)
                    ·
                      refine ⟨2538611385221638092663295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13539260721182069827537573 2538611385221638092663295)
                      ·
                        rfl

theorem cell23_4943928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_4943928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943928 prefixEnd_4943928 := by exact prefixLift 4943928
  have htrace : WordTrace (prefixWord ++ tailWord_4943928) baseStart_4943928 baseEnd_4943928 := by
    simpa [prefixWord, tailWord_4943928, baseEnd_4943928] using wordTrace_append hprefix tailTrace_4943928
  have hstable : (prefixWord ++ tailWord_4943928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943928).length < 2 ^ (prefixWord ++ tailWord_4943928).sum := by decide
  have hdescent : baseEnd_4943928 < baseStart_4943928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943931 : List Nat := [1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 3]
def baseStart_4943931 : Nat := 118140960795 + 4943931 * 2 ^ 59
def prefixEnd_4943931 : Nat := 4983230072969 + 3 ^ 40 * 4943931 * 2
def baseEnd_4943931 : Nat := 2538612925663601580925781

theorem tailTrace_4943931 : CollatzResearch.WordTrace tailWord_4943931 prefixEnd_4943931 2538612925663601580925781 := by
  unfold tailWord_4943931
  simp only [CollatzResearch.WordTrace]
  refine ⟨180319977451989818037279647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120213318301326545358186431 180319977451989818037279647)
  ·
    refine ⟨270479966177984727055919471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180319977451989818037279647 270479966177984727055919471)
    ·
      refine ⟨405719949266977090583879207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270479966177984727055919471 405719949266977090583879207)
      ·
        refine ⟨608579923900465635875818811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405719949266977090583879207 608579923900465635875818811)
        ·
          refine ⟨912869885850698453813728217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608579923900465635875818811 912869885850698453813728217)
          ·
            refine ⟨684652414388023840360296163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 912869885850698453813728217 684652414388023840360296163)
            ·
              refine ⟨1026978621582035760540444245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684652414388023840360296163 1026978621582035760540444245)
              ·
                refine ⟨12034905721664481568833331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1026978621582035760540444245 12034905721664481568833331)
                ·
                  refine ⟨18052358582496722353249997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12034905721664481568833331 18052358582496722353249997)
                  ·
                    refine ⟨6769634468436270882468749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18052358582496722353249997 6769634468436270882468749)
                    ·
                      refine ⟨2538612925663601580925781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6769634468436270882468749 2538612925663601580925781)
                      ·
                        rfl

theorem cell23_4943931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 3].length) (baseStart_4943931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943931 prefixEnd_4943931 := by exact prefixLift 4943931
  have htrace : WordTrace (prefixWord ++ tailWord_4943931) baseStart_4943931 baseEnd_4943931 := by
    simpa [prefixWord, tailWord_4943931, baseEnd_4943931] using wordTrace_append hprefix tailTrace_4943931
  have hstable : (prefixWord ++ tailWord_4943931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943931).length < 2 ^ (prefixWord ++ tailWord_4943931).sum := by decide
  have hdescent : baseEnd_4943931 < baseStart_4943931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943932 : List Nat := [2, 2, 2, 2, 2, 1, 2, 5, 1, 2, 2]
def baseStart_4943932 : Nat := 118140960795 + 4943932 * 2 ^ 59
def prefixEnd_4943932 : Nat := 4983230072969 + 3 ^ 40 * 4943932 * 2
def baseEnd_4943932 : Nat := 2538613439144256077013277

theorem tailTrace_4943932 : CollatzResearch.WordTrace tailWord_4943932 prefixEnd_4943932 2538613439144256077013277 := by
  unfold tailWord_4943932
  simp only [CollatzResearch.WordTrace]
  refine ⟨90160006962493097604033025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120213342616657463472044033 90160006962493097604033025)
  ·
    refine ⟨67620005221869823203024769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90160006962493097604033025 67620005221869823203024769)
    ·
      refine ⟨50715003916402367402268577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67620005221869823203024769 50715003916402367402268577)
      ·
        refine ⟨38036252937301775551701433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50715003916402367402268577 38036252937301775551701433)
        ·
          refine ⟨28527189702976331663776075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38036252937301775551701433 28527189702976331663776075)
          ·
            refine ⟨42790784554464497495664113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28527189702976331663776075 42790784554464497495664113)
            ·
              refine ⟨32093088415848373121748085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42790784554464497495664113 32093088415848373121748085)
              ·
                refine ⟨3008727038985784980163883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32093088415848373121748085 3008727038985784980163883)
                ·
                  refine ⟨4513090558478677470245825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3008727038985784980163883 4513090558478677470245825)
                  ·
                    refine ⟨3384817918859008102684369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4513090558478677470245825 3384817918859008102684369)
                    ·
                      refine ⟨2538613439144256077013277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3384817918859008102684369 2538613439144256077013277)
                      ·
                        rfl

theorem cell23_4943932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_4943932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943932 prefixEnd_4943932 := by exact prefixLift 4943932
  have htrace : WordTrace (prefixWord ++ tailWord_4943932) baseStart_4943932 baseEnd_4943932 := by
    simpa [prefixWord, tailWord_4943932, baseEnd_4943932] using wordTrace_append hprefix tailTrace_4943932
  have hstable : (prefixWord ++ tailWord_4943932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943932).length < 2 ^ (prefixWord ++ tailWord_4943932).sum := by decide
  have hdescent : baseEnd_4943932 < baseStart_4943932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943942 : List Nat := [6, 1, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_4943942 : Nat := 118140960795 + 4943942 * 2 ^ 59
def prefixEnd_4943942 : Nat := 4983230072969 + 3 ^ 40 * 4943942 * 2
def baseEnd_4943942 : Nat := 846206191316933679296077

theorem tailTrace_4943942 : CollatzResearch.WordTrace tailWord_4943942 prefixEnd_4943942 846206191316933679296077 := by
  unfold tailWord_4943942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5635011832967186466122815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 120213585769966644610620053 5635011832967186466122815)
  ·
    refine ⟨8452517749450779699184223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5635011832967186466122815 8452517749450779699184223)
    ·
      refine ⟨12678776624176169548776335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8452517749450779699184223 12678776624176169548776335)
      ·
        refine ⟨19018164936264254323164503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12678776624176169548776335 19018164936264254323164503)
        ·
          refine ⟨28527247404396381484746755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19018164936264254323164503 28527247404396381484746755)
          ·
            refine ⟨42790871106594572227120133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28527247404396381484746755 42790871106594572227120133)
            ·
              refine ⟨8023288332486482292585025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42790871106594572227120133 8023288332486482292585025)
              ·
                refine ⟨6017466249364861719438769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8023288332486482292585025 6017466249364861719438769)
                ·
                  refine ⟨4513099687023646289579077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6017466249364861719438769 4513099687023646289579077)
                  ·
                    refine ⟨846206191316933679296077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4513099687023646289579077 846206191316933679296077)
                    ·
                      rfl

theorem cell23_4943942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_4943942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943942 prefixEnd_4943942 := by exact prefixLift 4943942
  have htrace : WordTrace (prefixWord ++ tailWord_4943942) baseStart_4943942 baseEnd_4943942 := by
    simpa [prefixWord, tailWord_4943942, baseEnd_4943942] using wordTrace_append hprefix tailTrace_4943942
  have hstable : (prefixWord ++ tailWord_4943942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943942).length < 2 ^ (prefixWord ++ tailWord_4943942).sum := by decide
  have hdescent : baseEnd_4943942 < baseStart_4943942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943948 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 4, 1, 3]
def baseStart_4943948 : Nat := 118140960795 + 4943948 * 2 ^ 59
def prefixEnd_4943948 : Nat := 4983230072969 + 3 ^ 40 * 4943948 * 2
def baseEnd_4943948 : Nat := 2538621654834728014413203

theorem tailTrace_4943948 : CollatzResearch.WordTrace tailWord_4943948 prefixEnd_4943948 2538621654834728014413203 := by
  unfold tailWord_4943948
  simp only [CollatzResearch.WordTrace]
  refine ⟨90160298746464114970324249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120213731661952153293765665 90160298746464114970324249)
  ·
    refine ⟨67620224059848086227743187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90160298746464114970324249 67620224059848086227743187)
    ·
      refine ⟨101430336089772129341614781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67620224059848086227743187 101430336089772129341614781)
      ·
        refine ⟨38036376033664548503105543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101430336089772129341614781 38036376033664548503105543)
        ·
          refine ⟨57054564050496822754658315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38036376033664548503105543 57054564050496822754658315)
          ·
            refine ⟨85581846075745234131987473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57054564050496822754658315 85581846075745234131987473)
            ·
              refine ⟨64186384556808925598990605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85581846075745234131987473 64186384556808925598990605)
              ·
                refine ⟨24069894208803347099621477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64186384556808925598990605 24069894208803347099621477)
                ·
                  refine ⟨4513105164150627581179027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24069894208803347099621477 4513105164150627581179027)
                  ·
                    refine ⟨6769657746225941371768541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4513105164150627581179027 6769657746225941371768541)
                    ·
                      refine ⟨2538621654834728014413203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6769657746225941371768541 2538621654834728014413203)
                      ·
                        rfl

theorem cell23_4943948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_4943948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943948 prefixEnd_4943948 := by exact prefixLift 4943948
  have htrace : WordTrace (prefixWord ++ tailWord_4943948) baseStart_4943948 baseEnd_4943948 := by
    simpa [prefixWord, tailWord_4943948, baseEnd_4943948] using wordTrace_append hprefix tailTrace_4943948
  have hstable : (prefixWord ++ tailWord_4943948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943948).length < 2 ^ (prefixWord ++ tailWord_4943948).sum := by decide
  have hdescent : baseEnd_4943948 < baseStart_4943948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943949 : List Nat := [1, 6, 1, 1, 1, 1, 3, 4, 1, 2, 2]
def baseStart_4943949 : Nat := 118140960795 + 4943949 * 2 ^ 59
def prefixEnd_4943949 : Nat := 4983230072969 + 3 ^ 40 * 4943949 * 2
def baseEnd_4943949 : Nat := 2538622168315382510500699

theorem tailTrace_4943949 : CollatzResearch.WordTrace tailWord_4943949 prefixEnd_4943949 2538622168315382510500699 := by
  unfold tailWord_4943949
  simp only [CollatzResearch.WordTrace]
  refine ⟨180320633965924607111434901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120213755977283071407623267 180320633965924607111434901)
  ·
    refine ⟨8452529717152715958348511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 180320633965924607111434901 8452529717152715958348511)
    ·
      refine ⟨12678794575729073937522767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8452529717152715958348511 12678794575729073937522767)
      ·
        refine ⟨19018191863593610906284151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12678794575729073937522767 19018191863593610906284151)
        ·
          refine ⟨28527287795390416359426227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19018191863593610906284151 28527287795390416359426227)
          ·
            refine ⟨42790931693085624539139341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28527287795390416359426227 42790931693085624539139341)
            ·
              refine ⟨16046599384907109202177253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42790931693085624539139341 16046599384907109202177253)
              ·
                refine ⟨3008737384670082975408235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16046599384907109202177253 3008737384670082975408235)
                ·
                  refine ⟨4513106077005124463112353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3008737384670082975408235 4513106077005124463112353)
                  ·
                    refine ⟨3384829557753843347334265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4513106077005124463112353 3384829557753843347334265)
                    ·
                      refine ⟨2538622168315382510500699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3384829557753843347334265 2538622168315382510500699)
                      ·
                        rfl

theorem cell23_4943949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_4943949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943949 prefixEnd_4943949 := by exact prefixLift 4943949
  have htrace : WordTrace (prefixWord ++ tailWord_4943949) baseStart_4943949 baseEnd_4943949 := by
    simpa [prefixWord, tailWord_4943949, baseEnd_4943949] using wordTrace_append hprefix tailTrace_4943949
  have hstable : (prefixWord ++ tailWord_4943949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943949).length < 2 ^ (prefixWord ++ tailWord_4943949).sum := by decide
  have hdescent : baseEnd_4943949 < baseStart_4943949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943965 : List Nat := [1, 4, 4, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_4943965 : Nat := 118140960795 + 4943965 * 2 ^ 59
def prefixEnd_4943965 : Nat := 4983230072969 + 3 ^ 40 * 4943965 * 2
def baseEnd_4943965 : Nat := 2538630384005854447900625

theorem tailTrace_4943965 : CollatzResearch.WordTrace tailWord_4943965 prefixEnd_4943965 2538630384005854447900625 := by
  unfold tailWord_4943965
  simp only [CollatzResearch.WordTrace]
  refine ⟨180321217533866641844017349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120214145022577761229344899 180321217533866641844017349)
  ·
    refine ⟨33810228287599995345753253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180321217533866641844017349 33810228287599995345753253)
    ·
      refine ⟨6339417803924999127328735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33810228287599995345753253 6339417803924999127328735)
      ·
        refine ⟨9509126705887498690993103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6339417803924999127328735 9509126705887498690993103)
        ·
          refine ⟨14263690058831248036489655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9509126705887498690993103 14263690058831248036489655)
          ·
            refine ⟨21395535088246872054734483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14263690058831248036489655 21395535088246872054734483)
            ·
              refine ⟨32093302632370308082101725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21395535088246872054734483 32093302632370308082101725)
              ·
                refine ⟨12034988487138865530788147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32093302632370308082101725 12034988487138865530788147)
                ·
                  refine ⟨18052482730708298296182221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12034988487138865530788147 18052482730708298296182221)
                  ·
                    refine ⟨6769681024015611861068333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18052482730708298296182221 6769681024015611861068333)
                    ·
                      refine ⟨2538630384005854447900625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6769681024015611861068333 2538630384005854447900625)
                      ·
                        rfl

theorem cell23_4943965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_4943965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943965 prefixEnd_4943965 := by exact prefixLift 4943965
  have htrace : WordTrace (prefixWord ++ tailWord_4943965) baseStart_4943965 baseEnd_4943965 := by
    simpa [prefixWord, tailWord_4943965, baseEnd_4943965] using wordTrace_append hprefix tailTrace_4943965
  have hstable : (prefixWord ++ tailWord_4943965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943965).length < 2 ^ (prefixWord ++ tailWord_4943965).sum := by decide
  have hdescent : baseEnd_4943965 < baseStart_4943965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943966 : List Nat := [4, 4, 1, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_4943966 : Nat := 118140960795 + 4943966 * 2 ^ 59
def prefixEnd_4943966 : Nat := 4983230072969 + 3 ^ 40 * 4943966 * 2
def baseEnd_4943966 : Nat := 2538630897486508943988121

theorem tailTrace_4943966 : CollatzResearch.WordTrace tailWord_4943966 prefixEnd_4943966 2538630897486508943988121 := by
  unfold tailWord_4943966
  simp only [CollatzResearch.WordTrace]
  refine ⟨22540156750857877376850469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120214169337908679343202501 22540156750857877376850469)
  ·
    refine ⟨4226279390785852008159463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22540156750857877376850469 4226279390785852008159463)
    ·
      refine ⟨6339419086178778012239195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4226279390785852008159463 6339419086178778012239195)
      ·
        refine ⟨9509128629268167018358793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6339419086178778012239195 9509128629268167018358793)
        ·
          refine ⟨7131846471951125263769095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9509128629268167018358793 7131846471951125263769095)
          ·
            refine ⟨10697769707926687895653643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7131846471951125263769095 10697769707926687895653643)
            ·
              refine ⟨16046654561890031843480465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10697769707926687895653643 16046654561890031843480465)
              ·
                refine ⟨12034990921417523882610349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16046654561890031843480465 12034990921417523882610349)
                ·
                  refine ⟨4513121595531571455978881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12034990921417523882610349 4513121595531571455978881)
                  ·
                    refine ⟨3384841196648678591984161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4513121595531571455978881 3384841196648678591984161)
                    ·
                      refine ⟨2538630897486508943988121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3384841196648678591984161 2538630897486508943988121)
                      ·
                        rfl

theorem cell23_4943966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_4943966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943966 prefixEnd_4943966 := by exact prefixLift 4943966
  have htrace : WordTrace (prefixWord ++ tailWord_4943966) baseStart_4943966 baseEnd_4943966 := by
    simpa [prefixWord, tailWord_4943966, baseEnd_4943966] using wordTrace_append hprefix tailTrace_4943966
  have hstable : (prefixWord ++ tailWord_4943966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943966).length < 2 ^ (prefixWord ++ tailWord_4943966).sum := by decide
  have hdescent : baseEnd_4943966 < baseStart_4943966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943975 : List Nat := [1, 1, 5, 1, 1, 2, 2, 4, 1, 3, 2]
def baseStart_4943975 : Nat := 118140960795 + 4943975 * 2 ^ 59
def prefixEnd_4943975 : Nat := 4983230072969 + 3 ^ 40 * 4943975 * 2
def baseEnd_4943975 : Nat := 2538635518812399408775579

theorem tailTrace_4943975 : CollatzResearch.WordTrace tailWord_4943975 prefixEnd_4943975 2538635518812399408775579 := by
  unfold tailWord_4943975
  simp only [CollatzResearch.WordTrace]
  refine ⟨180321582263830413551881379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120214388175886942367920919 180321582263830413551881379)
  ·
    refine ⟨270482373395745620327822069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180321582263830413551881379 270482373395745620327822069)
    ·
      refine ⟨25357722505851151905733319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 270482373395745620327822069 25357722505851151905733319)
      ·
        refine ⟨38036583758776727858599979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25357722505851151905733319 38036583758776727858599979)
        ·
          refine ⟨57054875638165091787899969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38036583758776727858599979 57054875638165091787899969)
          ·
            refine ⟨42791156728623818840924977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57054875638165091787899969 42791156728623818840924977)
            ·
              refine ⟨32093367546467864130693733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42791156728623818840924977 32093367546467864130693733)
              ·
                refine ⟨6017506414962724524505075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32093367546467864130693733 6017506414962724524505075)
                ·
                  refine ⟨9026259622444086786757613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6017506414962724524505075 9026259622444086786757613)
                  ·
                    refine ⟨3384847358416532545034105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9026259622444086786757613 3384847358416532545034105)
                    ·
                      refine ⟨2538635518812399408775579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3384847358416532545034105 2538635518812399408775579)
                      ·
                        rfl

theorem cell23_4943975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_4943975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943975 prefixEnd_4943975 := by exact prefixLift 4943975
  have htrace : WordTrace (prefixWord ++ tailWord_4943975) baseStart_4943975 baseEnd_4943975 := by
    simpa [prefixWord, tailWord_4943975, baseEnd_4943975] using wordTrace_append hprefix tailTrace_4943975
  have hstable : (prefixWord ++ tailWord_4943975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943975).length < 2 ^ (prefixWord ++ tailWord_4943975).sum := by decide
  have hdescent : baseEnd_4943975 < baseStart_4943975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4943981 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_4943981 : Nat := 118140960795 + 4943981 * 2 ^ 59
def prefixEnd_4943981 : Nat := 4983230072969 + 3 ^ 40 * 4943981 * 2
def baseEnd_4943981 : Nat := 846212866565442128433517

theorem tailTrace_4943981 : CollatzResearch.WordTrace tailWord_4943981 prefixEnd_4943981 846212866565442128433517 := by
  unfold tailWord_4943981
  simp only [CollatzResearch.WordTrace]
  refine ⟨180321801101808676576599797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120214534067872451051066531 180321801101808676576599797)
  ·
    refine ⟨16905168853294563429056231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 180321801101808676576599797 16905168853294563429056231)
    ·
      refine ⟨25357753279941845143584347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16905168853294563429056231 25357753279941845143584347)
      ·
        refine ⟨38036629919912767715376521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25357753279941845143584347 38036629919912767715376521)
        ·
          refine ⟨28527472439934575786532391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38036629919912767715376521 28527472439934575786532391)
          ·
            refine ⟨42791208659901863679798587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28527472439934575786532391 42791208659901863679798587)
            ·
              refine ⟨64186812989852795519697881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42791208659901863679798587 64186812989852795519697881)
              ·
                refine ⟨48140109742389596639773411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64186812989852795519697881 48140109742389596639773411)
                ·
                  refine ⟨72210164613584394959660117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48140109742389596639773411 72210164613584394959660117)
                  ·
                    refine ⟨846212866565442128433517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72210164613584394959660117 846212866565442128433517)
                    ·
                      rfl

theorem cell23_4943981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_4943981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4943981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4943981 prefixEnd_4943981 := by exact prefixLift 4943981
  have htrace : WordTrace (prefixWord ++ tailWord_4943981) baseStart_4943981 baseEnd_4943981 := by
    simpa [prefixWord, tailWord_4943981, baseEnd_4943981] using wordTrace_append hprefix tailTrace_4943981
  have hstable : (prefixWord ++ tailWord_4943981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4943981).length < 2 ^ (prefixWord ++ tailWord_4943981).sum := by decide
  have hdescent : baseEnd_4943981 < baseStart_4943981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4943981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944018 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_4944018 : Nat := 118140960795 + 4944018 * 2 ^ 59
def prefixEnd_4944018 : Nat := 4983230072969 + 3 ^ 40 * 4944018 * 2
def baseEnd_4944018 : Nat := 2538657598480542740537881

theorem tailTrace_4944018 : CollatzResearch.WordTrace tailWord_4944018 prefixEnd_4944018 2538657598480542740537881 := by
  unfold tailWord_4944018
  simp only [CollatzResearch.WordTrace]
  refine ⟨45080787650668657973924177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120215433735116421263797805 45080787650668657973924177)
  ·
    refine ⟨33810590738001493480443133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45080787650668657973924177 33810590738001493480443133)
    ·
      refine ⟨12678971526750560055166175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33810590738001493480443133 12678971526750560055166175)
      ·
        refine ⟨19018457290125840082749263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12678971526750560055166175 19018457290125840082749263)
        ·
          refine ⟨28527685935188760124123895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19018457290125840082749263 28527685935188760124123895)
          ·
            refine ⟨42791528902783140186185843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28527685935188760124123895 42791528902783140186185843)
            ·
              refine ⟨64187293354174710279278765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42791528902783140186185843 64187293354174710279278765)
              ·
                refine ⟨24070235007815516354729537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64187293354174710279278765 24070235007815516354729537)
                ·
                  refine ⟨18052676255861637266047153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24070235007815516354729537 18052676255861637266047153)
                  ·
                    refine ⟨13539507191896227949535365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18052676255861637266047153 13539507191896227949535365)
                    ·
                      refine ⟨2538657598480542740537881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13539507191896227949535365 2538657598480542740537881)
                      ·
                        rfl

theorem cell23_4944018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_4944018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944018 prefixEnd_4944018 := by exact prefixLift 4944018
  have htrace : WordTrace (prefixWord ++ tailWord_4944018) baseStart_4944018 baseEnd_4944018 := by
    simpa [prefixWord, tailWord_4944018, baseEnd_4944018] using wordTrace_append hprefix tailTrace_4944018
  have hstable : (prefixWord ++ tailWord_4944018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944018).length < 2 ^ (prefixWord ++ tailWord_4944018).sum := by decide
  have hdescent : baseEnd_4944018 < baseStart_4944018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944051 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 5]
def baseStart_4944051 : Nat := 118140960795 + 4944051 * 2 ^ 59
def prefixEnd_4944051 : Nat := 4983230072969 + 3 ^ 40 * 4944051 * 2
def baseEnd_4944051 : Nat := 2538674543342141111425229

theorem tailTrace_4944051 : CollatzResearch.WordTrace tailWord_4944051 prefixEnd_4944051 2538674543342141111425229 := by
  unfold tailWord_4944051
  simp only [CollatzResearch.WordTrace]
  refine ⟨180324354211555078531648007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120216236141036719021098671 180324354211555078531648007)
  ·
    refine ⟨270486531317332617797472011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180324354211555078531648007 270486531317332617797472011)
    ·
      refine ⟨405729796975998926696208017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270486531317332617797472011 405729796975998926696208017)
      ·
        refine ⟨304297347731999195022156013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 405729796975998926696208017 304297347731999195022156013)
        ·
          refine ⟨114111505399499698133308505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 304297347731999195022156013 114111505399499698133308505)
          ·
            refine ⟨85583629049624773599981379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114111505399499698133308505 85583629049624773599981379)
            ·
              refine ⟨128375443574437160399972069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85583629049624773599981379 128375443574437160399972069)
              ·
                refine ⟨24070395670206967574994763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128375443574437160399972069 24070395670206967574994763)
                ·
                  refine ⟨36105593505310451362492145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24070395670206967574994763 36105593505310451362492145)
                  ·
                    refine ⟨27079195128982838521869109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36105593505310451362492145 27079195128982838521869109)
                    ·
                      refine ⟨2538674543342141111425229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27079195128982838521869109 2538674543342141111425229)
                      ·
                        rfl

theorem cell23_4944051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_4944051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944051 prefixEnd_4944051 := by exact prefixLift 4944051
  have htrace : WordTrace (prefixWord ++ tailWord_4944051) baseStart_4944051 baseEnd_4944051 := by
    simpa [prefixWord, tailWord_4944051, baseEnd_4944051] using wordTrace_append hprefix tailTrace_4944051
  have hstable : (prefixWord ++ tailWord_4944051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944051).length < 2 ^ (prefixWord ++ tailWord_4944051).sum := by decide
  have hdescent : baseEnd_4944051 < baseStart_4944051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944062 : List Nat := [4, 2, 1, 1, 5, 1, 1, 1, 7]
def baseStart_4944062 : Nat := 118140960795 + 4944062 * 2 ^ 59
def prefixEnd_4944062 : Nat := 4983230072969 + 3 ^ 40 * 4944062 * 2
def baseEnd_4944062 : Nat := 282075576847704507598631

theorem tailTrace_4944062 : CollatzResearch.WordTrace tailWord_4944062 prefixEnd_4944062 282075576847704507598631 := by
  unfold tailWord_4944062
  simp only [CollatzResearch.WordTrace]
  refine ⟨22540594426814403426287305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120216503609676818273532293 22540594426814403426287305)
  ·
    refine ⟨16905445820110802569715479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22540594426814403426287305 16905445820110802569715479)
    ·
      refine ⟨25358168730166203854573219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16905445820110802569715479 25358168730166203854573219)
      ·
        refine ⟨38037253095249305781859829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25358168730166203854573219 38037253095249305781859829)
        ·
          refine ⟨3565992477679622417049359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38037253095249305781859829 3565992477679622417049359)
          ·
            refine ⟨5348988716519433625574039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3565992477679622417049359 5348988716519433625574039)
            ·
              refine ⟨8023483074779150438361059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5348988716519433625574039 8023483074779150438361059)
              ·
                refine ⟨12035224612168725657541589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8023483074779150438361059 12035224612168725657541589)
                ·
                  refine ⟨282075576847704507598631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12035224612168725657541589 282075576847704507598631)
                  ·
                    rfl

theorem cell23_4944062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_4944062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944062 prefixEnd_4944062 := by exact prefixLift 4944062
  have htrace : WordTrace (prefixWord ++ tailWord_4944062) baseStart_4944062 baseEnd_4944062 := by
    simpa [prefixWord, tailWord_4944062, baseEnd_4944062] using wordTrace_append hprefix tailTrace_4944062
  have hstable : (prefixWord ++ tailWord_4944062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944062).length < 2 ^ (prefixWord ++ tailWord_4944062).sum := by decide
  have hdescent : baseEnd_4944062 < baseStart_4944062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944068 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_4944068 : Nat := 118140960795 + 4944068 * 2 ^ 59
def prefixEnd_4944068 : Nat := 4983230072969 + 3 ^ 40 * 4944068 * 2
def baseEnd_4944068 : Nat := 2538683272513267544912651

theorem tailTrace_4944068 : CollatzResearch.WordTrace tailWord_4944068 prefixEnd_4944068 2538683272513267544912651 := by
  unfold tailWord_4944068
  simp only [CollatzResearch.WordTrace]
  refine ⟨90162487126246745217508429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120216649501662326956677905 90162487126246745217508429)
  ·
    refine ⟨33810932672342529456565661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90162487126246745217508429 33810932672342529456565661)
    ·
      refine ⟨12679099752128448546212123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33810932672342529456565661 12679099752128448546212123)
      ·
        refine ⟨19018649628192672819318185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12679099752128448546212123 19018649628192672819318185)
        ·
          refine ⟨14263987221144504614488639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19018649628192672819318185 14263987221144504614488639)
          ·
            refine ⟨21395980831716756921732959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14263987221144504614488639 21395980831716756921732959)
            ·
              refine ⟨32093971247575135382599439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21395980831716756921732959 32093971247575135382599439)
              ·
                refine ⟨48140956871362703073899159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32093971247575135382599439 48140956871362703073899159)
                ·
                  refine ⟨72211435307044054610848739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48140956871362703073899159 72211435307044054610848739)
                  ·
                    refine ⟨108317152960566081916273109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72211435307044054610848739 108317152960566081916273109)
                    ·
                      refine ⟨2538683272513267544912651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108317152960566081916273109 2538683272513267544912651)
                      ·
                        rfl

theorem cell23_4944068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_4944068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944068 prefixEnd_4944068 := by exact prefixLift 4944068
  have htrace : WordTrace (prefixWord ++ tailWord_4944068) baseStart_4944068 baseEnd_4944068 := by
    simpa [prefixWord, tailWord_4944068, baseEnd_4944068] using wordTrace_append hprefix tailTrace_4944068
  have hstable : (prefixWord ++ tailWord_4944068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944068).length < 2 ^ (prefixWord ++ tailWord_4944068).sum := by decide
  have hdescent : baseEnd_4944068 < baseStart_4944068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944091 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 4]
def baseStart_4944091 : Nat := 118140960795 + 4944091 * 2 ^ 59
def prefixEnd_4944091 : Nat := 4983230072969 + 3 ^ 40 * 4944091 * 2
def baseEnd_4944091 : Nat := 2538695082568320954925045

theorem tailTrace_4944091 : CollatzResearch.WordTrace tailWord_4944091 prefixEnd_4944091 2538695082568320954925045 := by
  unfold tailWord_4944091
  simp only [CollatzResearch.WordTrace]
  refine ⟨180325813131410165363104127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120217208754273443575402751 180325813131410165363104127)
  ·
    refine ⟨270488719697115248044656191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180325813131410165363104127 270488719697115248044656191)
    ·
      refine ⟨405733079545672872066984287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270488719697115248044656191 405733079545672872066984287)
      ·
        refine ⟨608599619318509308100476431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405733079545672872066984287 608599619318509308100476431)
        ·
          refine ⟨912899428977763962150714647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608599619318509308100476431 912899428977763962150714647)
          ·
            refine ⟨1369349143466645943226071971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912899428977763962150714647 1369349143466645943226071971)
            ·
              refine ⟨2054023715199968914839107957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369349143466645943226071971 2054023715199968914839107957)
              ·
                refine ⟨192564723299997085766166371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2054023715199968914839107957 192564723299997085766166371)
                ·
                  refine ⟨288847084949995628649249557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192564723299997085766166371 288847084949995628649249557)
                  ·
                    refine ⟨13539707107031045092933573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 288847084949995628649249557 13539707107031045092933573)
                    ·
                      refine ⟨2538695082568320954925045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13539707107031045092933573 2538695082568320954925045)
                      ·
                        rfl

theorem cell23_4944091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 4].length) (baseStart_4944091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944091 prefixEnd_4944091 := by exact prefixLift 4944091
  have htrace : WordTrace (prefixWord ++ tailWord_4944091) baseStart_4944091 baseEnd_4944091 := by
    simpa [prefixWord, tailWord_4944091, baseEnd_4944091] using wordTrace_append hprefix tailTrace_4944091
  have hstable : (prefixWord ++ tailWord_4944091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944091).length < 2 ^ (prefixWord ++ tailWord_4944091).sum := by decide
  have hdescent : baseEnd_4944091 < baseStart_4944091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944118 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 8]
def baseStart_4944118 : Nat := 118140960795 + 4944118 * 2 ^ 59
def prefixEnd_4944118 : Nat := 4983230072969 + 3 ^ 40 * 4944118 * 2
def baseEnd_4944118 : Nat := 282078771838443594365269

theorem tailTrace_4944118 : CollatzResearch.WordTrace tailWord_4944118 prefixEnd_4944118 282078771838443594365269 := by
  unfold tailWord_4944118
  simp only [CollatzResearch.WordTrace]
  refine ⟨11270424868894521810896063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120217865268208232649558005 11270424868894521810896063)
  ·
    refine ⟨16905637303341782716344095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11270424868894521810896063 16905637303341782716344095)
    ·
      refine ⟨25358455955012674074516143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16905637303341782716344095 25358455955012674074516143)
      ·
        refine ⟨38037683932519011111774215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25358455955012674074516143 38037683932519011111774215)
        ·
          refine ⟨57056525898778516667661323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38037683932519011111774215 57056525898778516667661323)
          ·
            refine ⟨85584788848167775001491985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57056525898778516667661323 85584788848167775001491985)
            ·
              refine ⟨64188591636125831251118989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85584788848167775001491985 64188591636125831251118989)
              ·
                refine ⟨24070721863547186719169621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64188591636125831251118989 24070721863547186719169621)
                ·
                  refine ⟨282078771838443594365269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24070721863547186719169621 282078771838443594365269)
                  ·
                    rfl

theorem cell23_4944118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_4944118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944118 prefixEnd_4944118 := by exact prefixLift 4944118
  have htrace : WordTrace (prefixWord ++ tailWord_4944118) baseStart_4944118 baseEnd_4944118 := by
    simpa [prefixWord, tailWord_4944118, baseEnd_4944118] using wordTrace_append hprefix tailTrace_4944118
  have hstable : (prefixWord ++ tailWord_4944118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944118).length < 2 ^ (prefixWord ++ tailWord_4944118).sum := by decide
  have hdescent : baseEnd_4944118 < baseStart_4944118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944122 : List Nat := [3, 1, 1, 1, 1, 6, 1, 4, 1, 4]
def baseStart_4944122 : Nat := 118140960795 + 4944122 * 2 ^ 59
def prefixEnd_4944122 : Nat := 4983230072969 + 3 ^ 40 * 4944122 * 2
def baseEnd_4944122 : Nat := 846237000156203444545801

theorem tailTrace_4944122 : CollatzResearch.WordTrace tailWord_4944122 prefixEnd_4944122 846237000156203444545801 := by
  unfold tailWord_4944122
  simp only [CollatzResearch.WordTrace]
  refine ⟨45081735948574464414370655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120217962529531905104988413 45081735948574464414370655)
  ·
    refine ⟨67622603922861696621555983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45081735948574464414370655 67622603922861696621555983)
    ·
      refine ⟨101433905884292544932333975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67622603922861696621555983 101433905884292544932333975)
      ·
        refine ⟨152150858826438817398500963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101433905884292544932333975 152150858826438817398500963)
        ·
          refine ⟨228226288239658226097751445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152150858826438817398500963 228226288239658226097751445)
          ·
            refine ⟨10698107261233979348332099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 228226288239658226097751445 10698107261233979348332099)
            ·
              refine ⟨16047160891850969022498149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10698107261233979348332099 16047160891850969022498149)
              ·
                refine ⟨3008842667222056691718403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16047160891850969022498149 3008842667222056691718403)
                ·
                  refine ⟨4513264000833085037577605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3008842667222056691718403 4513264000833085037577605)
                  ·
                    refine ⟨846237000156203444545801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4513264000833085037577605 846237000156203444545801)
                    ·
                      rfl

theorem cell23_4944122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 1, 4].length) (baseStart_4944122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944122 prefixEnd_4944122 := by exact prefixLift 4944122
  have htrace : WordTrace (prefixWord ++ tailWord_4944122) baseStart_4944122 baseEnd_4944122 := by
    simpa [prefixWord, tailWord_4944122, baseEnd_4944122] using wordTrace_append hprefix tailTrace_4944122
  have hstable : (prefixWord ++ tailWord_4944122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944122).length < 2 ^ (prefixWord ++ tailWord_4944122).sum := by decide
  have hdescent : baseEnd_4944122 < baseStart_4944122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944145 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 5, 1, 3]
def baseStart_4944145 : Nat := 118140960795 + 4944145 * 2 ^ 59
def prefixEnd_4944145 : Nat := 4983230072969 + 3 ^ 40 * 4944145 * 2
def baseEnd_4944145 : Nat := 2538722810523663743649797

theorem tailTrace_4944145 : CollatzResearch.WordTrace tailWord_4944145 prefixEnd_4944145 2538722810523663743649797 := by
  unfold tailWord_4944145
  simp only [CollatzResearch.WordTrace]
  refine ⟨180327782673214532585569889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120218521782143021723713259 180327782673214532585569889)
  ·
    refine ⟨135245837004910899439177417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180327782673214532585569889 135245837004910899439177417)
    ·
      refine ⟨101434377753683174579383063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135245837004910899439177417 101434377753683174579383063)
      ·
        refine ⟨152151566630524761869074595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101434377753683174579383063 152151566630524761869074595)
        ·
          refine ⟨228227349945787142803611893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152151566630524761869074595 228227349945787142803611893)
          ·
            refine ⟨21396314057417544637838615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 228227349945787142803611893 21396314057417544637838615)
            ·
              refine ⟨32094471086126316956757923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21396314057417544637838615 32094471086126316956757923)
              ·
                refine ⟨48141706629189475435136885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32094471086126316956757923 48141706629189475435136885)
                ·
                  refine ⟨4513284996486513322044083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48141706629189475435136885 4513284996486513322044083)
                  ·
                    refine ⟨6769927494729769983066125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4513284996486513322044083 6769927494729769983066125)
                    ·
                      refine ⟨2538722810523663743649797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6769927494729769983066125 2538722810523663743649797)
                      ·
                        rfl

theorem cell23_4944145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 1, 3].length) (baseStart_4944145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944145 prefixEnd_4944145 := by exact prefixLift 4944145
  have htrace : WordTrace (prefixWord ++ tailWord_4944145) baseStart_4944145 baseEnd_4944145 := by
    simpa [prefixWord, tailWord_4944145, baseEnd_4944145] using wordTrace_append hprefix tailTrace_4944145
  have hstable : (prefixWord ++ tailWord_4944145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944145).length < 2 ^ (prefixWord ++ tailWord_4944145).sum := by decide
  have hdescent : baseEnd_4944145 < baseStart_4944145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944195 : List Nat := [1, 1, 1, 3, 1, 3, 2, 5, 2, 4]
def baseStart_4944195 : Nat := 118140960795 + 4944195 * 2 ^ 59
def prefixEnd_4944195 : Nat := 4983230072969 + 3 ^ 40 * 4944195 * 2
def baseEnd_4944195 : Nat := 846249494852129516008189

theorem tailTrace_4944195 : CollatzResearch.WordTrace tailWord_4944195 prefixEnd_4944195 846249494852129516008189 := by
  unfold tailWord_4944195
  simp only [CollatzResearch.WordTrace]
  refine ⟨180329606323033391124890039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120219737548688927416593359 180329606323033391124890039)
  ·
    refine ⟨270494409484550086687335059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180329606323033391124890039 270494409484550086687335059)
    ·
      refine ⟨405741614226825130031002589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270494409484550086687335059 405741614226825130031002589)
      ·
        refine ⟨152153105335059423761625971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 405741614226825130031002589 152153105335059423761625971)
        ·
          refine ⟨228229658002589135642438957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152153105335059423761625971 228229658002589135642438957)
          ·
            refine ⟨85586121750970925865914609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228229658002589135642438957 85586121750970925865914609)
            ·
              refine ⟨64189591313228194399435957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85586121750970925865914609 64189591313228194399435957)
              ·
                refine ⟨6017774185615143224947121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64189591313228194399435957 6017774185615143224947121)
                ·
                  refine ⟨4513330639211357418710341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6017774185615143224947121 4513330639211357418710341)
                  ·
                    refine ⟨846249494852129516008189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4513330639211357418710341 846249494852129516008189)
                    ·
                      rfl

theorem cell23_4944195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 4].length) (baseStart_4944195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944195 prefixEnd_4944195 := by exact prefixLift 4944195
  have htrace : WordTrace (prefixWord ++ tailWord_4944195) baseStart_4944195 baseEnd_4944195 := by
    simpa [prefixWord, tailWord_4944195, baseEnd_4944195] using wordTrace_append hprefix tailTrace_4944195
  have hstable : (prefixWord ++ tailWord_4944195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944195).length < 2 ^ (prefixWord ++ tailWord_4944195).sum := by decide
  have hdescent : baseEnd_4944195 < baseStart_4944195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944208 : List Nat := [2, 1, 1, 1, 1, 7, 1, 9]
def baseStart_4944208 : Nat := 118140960795 + 4944208 * 2 ^ 59
def prefixEnd_4944208 : Nat := 4983230072969 + 3 ^ 40 * 4944208 * 2
def baseEnd_4944208 : Nat := 94027968881662851746741

theorem tailTrace_4944208 : CollatzResearch.WordTrace tailWord_4944208 prefixEnd_4944208 94027968881662851746741 := by
  unfold tailWord_4944208
  simp only [CollatzResearch.WordTrace]
  refine ⟨90165040235993147172556639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120220053647990862896742185 90165040235993147172556639)
  ·
    refine ⟨135247560353989720758834959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90165040235993147172556639 135247560353989720758834959)
    ·
      refine ⟨202871340530984581138252439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135247560353989720758834959 202871340530984581138252439)
      ·
        refine ⟨304307010796476871707378659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202871340530984581138252439 304307010796476871707378659)
        ·
          refine ⟨456460516194715307561067989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304307010796476871707378659 456460516194715307561067989)
          ·
            refine ⟨10698293348313640020962531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 456460516194715307561067989 10698293348313640020962531)
            ·
              refine ⟨16047440022470460031443797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10698293348313640020962531 16047440022470460031443797)
              ·
                refine ⟨94027968881662851746741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16047440022470460031443797 94027968881662851746741)
                ·
                  rfl

theorem cell23_4944208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 9].length) (baseStart_4944208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944208 prefixEnd_4944208 := by exact prefixLift 4944208
  have htrace : WordTrace (prefixWord ++ tailWord_4944208) baseStart_4944208 baseEnd_4944208 := by
    simpa [prefixWord, tailWord_4944208, baseEnd_4944208] using wordTrace_append hprefix tailTrace_4944208
  have hstable : (prefixWord ++ tailWord_4944208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944208).length < 2 ^ (prefixWord ++ tailWord_4944208).sum := by decide
  have hdescent : baseEnd_4944208 < baseStart_4944208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944213 : List Nat := [1, 3, 2, 2, 5, 1, 1, 3, 1, 1, 3]
def baseStart_4944213 : Nat := 118140960795 + 4944213 * 2 ^ 59
def prefixEnd_4944213 : Nat := 4983230072969 + 3 ^ 40 * 4944213 * 2
def baseEnd_4944213 : Nat := 2538757727208169477599485

theorem tailTrace_4944213 : CollatzResearch.WordTrace tailWord_4944213 prefixEnd_4944213 2538757727208169477599485 := by
  unfold tailWord_4944213
  simp only [CollatzResearch.WordTrace]
  refine ⟨180330262836968180199045293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120220175224645453466030195 180330262836968180199045293)
  ·
    refine ⟨67623848563863067574641985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180330262836968180199045293 67623848563863067574641985)
    ·
      refine ⟨50717886422897300680981489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67623848563863067574641985 50717886422897300680981489)
      ·
        refine ⟨38038414817172975510736117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50717886422897300680981489 38038414817172975510736117)
        ·
          refine ⟨3566101389109966454131511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38038414817172975510736117 3566101389109966454131511)
          ·
            refine ⟨5349152083664949681197267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3566101389109966454131511 5349152083664949681197267)
            ·
              refine ⟨8023728125497424521795901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5349152083664949681197267 8023728125497424521795901)
              ·
                refine ⟨3008898047061534195673463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8023728125497424521795901 3008898047061534195673463)
                ·
                  refine ⟨4513347070592301293510195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3008898047061534195673463 4513347070592301293510195)
                  ·
                    refine ⟨6770020605888451940265293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4513347070592301293510195 6770020605888451940265293)
                    ·
                      refine ⟨2538757727208169477599485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6770020605888451940265293 2538757727208169477599485)
                      ·
                        rfl

theorem cell23_4944213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_4944213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944213 prefixEnd_4944213 := by exact prefixLift 4944213
  have htrace : WordTrace (prefixWord ++ tailWord_4944213) baseStart_4944213 baseEnd_4944213 := by
    simpa [prefixWord, tailWord_4944213, baseEnd_4944213] using wordTrace_append hprefix tailTrace_4944213
  have hstable : (prefixWord ++ tailWord_4944213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944213).length < 2 ^ (prefixWord ++ tailWord_4944213).sum := by decide
  have hdescent : baseEnd_4944213 < baseStart_4944213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944236 : List Nat := [2, 2, 1, 1, 6, 2, 1, 1, 3, 2, 2]
def baseStart_4944236 : Nat := 118140960795 + 4944236 * 2 ^ 59
def prefixEnd_4944236 : Nat := 4983230072969 + 3 ^ 40 * 4944236 * 2
def baseEnd_4944236 : Nat := 2538769537263222887611879

theorem tailTrace_4944236 : CollatzResearch.WordTrace tailWord_4944236 prefixEnd_4944236 2538769537263222887611879 := by
  unfold tailWord_4944236
  simp only [CollatzResearch.WordTrace]
  refine ⟨90165550857942427563566281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120220734477256570084755041 90165550857942427563566281)
  ·
    refine ⟨67624163143456820672674711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90165550857942427563566281 67624163143456820672674711)
    ·
      refine ⟨101436244715185231009012067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67624163143456820672674711 101436244715185231009012067)
      ·
        refine ⟨152154367072777846513518101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101436244715185231009012067 152154367072777846513518101)
        ·
          refine ⟨7132235956536461555321161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 152154367072777846513518101 7132235956536461555321161)
          ·
            refine ⟨5349176967402346166490871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7132235956536461555321161 5349176967402346166490871)
            ·
              refine ⟨8023765451103519249736307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5349176967402346166490871 8023765451103519249736307)
              ·
                refine ⟨12035648176655278874604461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8023765451103519249736307 12035648176655278874604461)
                ·
                  refine ⟨4513368066245729577976673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12035648176655278874604461 4513368066245729577976673)
                  ·
                    refine ⟨3385026049684297183482505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4513368066245729577976673 3385026049684297183482505)
                    ·
                      refine ⟨2538769537263222887611879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3385026049684297183482505 2538769537263222887611879)
                      ·
                        rfl

theorem cell23_4944236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 2, 2].length) (baseStart_4944236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944236 prefixEnd_4944236 := by exact prefixLift 4944236
  have htrace : WordTrace (prefixWord ++ tailWord_4944236) baseStart_4944236 baseEnd_4944236 := by
    simpa [prefixWord, tailWord_4944236, baseEnd_4944236] using wordTrace_append hprefix tailTrace_4944236
  have hstable : (prefixWord ++ tailWord_4944236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944236).length < 2 ^ (prefixWord ++ tailWord_4944236).sum := by decide
  have hdescent : baseEnd_4944236 < baseStart_4944236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944246 : List Nat := [5, 1, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_4944246 : Nat := 118140960795 + 4944246 * 2 ^ 59
def prefixEnd_4944246 : Nat := 4983230072969 + 3 ^ 40 * 4944246 * 2
def baseEnd_4944246 : Nat := 846258224023255949495611

theorem tailTrace_4944246 : CollatzResearch.WordTrace tailWord_4944246 prefixEnd_4944246 846258224023255949495611 := by
  unfold tailWord_4944246
  simp only [CollatzResearch.WordTrace]
  refine ⟨11270716652865539177187287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120220977630565751223331061 11270716652865539177187287)
  ·
    refine ⟨16906074979298308765780931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11270716652865539177187287 16906074979298308765780931)
    ·
      refine ⟨25359112468947463148671397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16906074979298308765780931 25359112468947463148671397)
      ·
        refine ⟨4754833587927649340375887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25359112468947463148671397 4754833587927649340375887)
        ·
          refine ⟨7132250381891474010563831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4754833587927649340375887 7132250381891474010563831)
          ·
            refine ⟨10698375572837211015845747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7132250381891474010563831 10698375572837211015845747)
            ·
              refine ⟨16047563359255816523768621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10698375572837211015845747 16047563359255816523768621)
              ·
                refine ⟨6017836259720931196413233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16047563359255816523768621 6017836259720931196413233)
                ·
                  refine ⟨4513377194790698397309925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6017836259720931196413233 4513377194790698397309925)
                  ·
                    refine ⟨846258224023255949495611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4513377194790698397309925 846258224023255949495611)
                    ·
                      rfl

theorem cell23_4944246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_4944246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944246 prefixEnd_4944246 := by exact prefixLift 4944246
  have htrace : WordTrace (prefixWord ++ tailWord_4944246) baseStart_4944246 baseEnd_4944246 := by
    simpa [prefixWord, tailWord_4944246, baseEnd_4944246] using wordTrace_append hprefix tailTrace_4944246
  have hstable : (prefixWord ++ tailWord_4944246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944246).length < 2 ^ (prefixWord ++ tailWord_4944246).sum := by decide
  have hdescent : baseEnd_4944246 < baseStart_4944246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944286 : List Nat := [4, 3, 1, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_4944286 : Nat := 118140960795 + 4944286 * 2 ^ 59
def prefixEnd_4944286 : Nat := 4983230072969 + 3 ^ 40 * 4944286 * 2
def baseEnd_4944286 : Nat := 2538795211295947691986649

theorem tailTrace_4944286 : CollatzResearch.WordTrace tailWord_4944286 prefixEnd_4944286 2538795211295947691986649 := by
  unfold tailWord_4944286
  simp only [CollatzResearch.WordTrace]
  refine ⟨22541615670712964208306589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120221950243802475777635141 22541615670712964208306589)
  ·
    refine ⟨8453105876517361578114971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22541615670712964208306589 8453105876517361578114971)
    ·
      refine ⟨12679658814776042367172457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8453105876517361578114971 12679658814776042367172457)
      ·
        refine ⟨9509744111082031775379343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12679658814776042367172457 9509744111082031775379343)
        ·
          refine ⟨14264616166623047663069015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9509744111082031775379343 14264616166623047663069015)
          ·
            refine ⟨21396924249934571494603523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14264616166623047663069015 21396924249934571494603523)
            ·
              refine ⟨32095386374901857241905285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21396924249934571494603523 32095386374901857241905285)
              ·
                refine ⟨6017884945294098232857241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32095386374901857241905285 6017884945294098232857241)
                ·
                  refine ⟨4513413708970573674642931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6017884945294098232857241 4513413708970573674642931)
                  ·
                    refine ⟨6770120563455860511964397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4513413708970573674642931 6770120563455860511964397)
                    ·
                      refine ⟨2538795211295947691986649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6770120563455860511964397 2538795211295947691986649)
                      ·
                        rfl

theorem cell23_4944286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_4944286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944286 prefixEnd_4944286 := by exact prefixLift 4944286
  have htrace : WordTrace (prefixWord ++ tailWord_4944286) baseStart_4944286 baseEnd_4944286 := by
    simpa [prefixWord, tailWord_4944286, baseEnd_4944286] using wordTrace_append hprefix tailTrace_4944286
  have hstable : (prefixWord ++ tailWord_4944286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944286).length < 2 ^ (prefixWord ++ tailWord_4944286).sum := by decide
  have hdescent : baseEnd_4944286 < baseStart_4944286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944305 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 1, 4, 4]
def baseStart_4944305 : Nat := 118140960795 + 4944305 * 2 ^ 59
def prefixEnd_4944305 : Nat := 4983230072969 + 3 ^ 40 * 4944305 * 2
def baseEnd_4944305 : Nat := 2538804967428383117649061

theorem tailTrace_4944305 : CollatzResearch.WordTrace tailWord_4944305 prefixEnd_4944305 2538804967428383117649061 := by
  unfold tailWord_4944305
  simp only [CollatzResearch.WordTrace]
  refine ⟨180333618352634879911394369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120222412235089919940929579 180333618352634879911394369)
  ·
    refine ⟨135250213764476159933545777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180333618352634879911394369 135250213764476159933545777)
    ·
      refine ⟨101437660323357119950159333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135250213764476159933545777 101437660323357119950159333)
      ·
        refine ⟨19019561310629459990654875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101437660323357119950159333 19019561310629459990654875)
        ·
          refine ⟨28529341965944189985982313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19019561310629459990654875 28529341965944189985982313)
          ·
            refine ⟨21397006474458142489486735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28529341965944189985982313 21397006474458142489486735)
            ·
              refine ⟨32095509711687213734230103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21397006474458142489486735 32095509711687213734230103)
              ·
                refine ⟨48143264567530820601345155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32095509711687213734230103 48143264567530820601345155)
                ·
                  refine ⟨72214896851296230902017733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48143264567530820601345155 72214896851296230902017733)
                  ·
                    refine ⟨13540293159618043294128325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72214896851296230902017733 13540293159618043294128325)
                    ·
                      refine ⟨2538804967428383117649061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13540293159618043294128325 2538804967428383117649061)
                      ·
                        rfl

theorem cell23_4944305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_4944305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944305 prefixEnd_4944305 := by exact prefixLift 4944305
  have htrace : WordTrace (prefixWord ++ tailWord_4944305) baseStart_4944305 baseEnd_4944305 := by
    simpa [prefixWord, tailWord_4944305, baseEnd_4944305] using wordTrace_append hprefix tailTrace_4944305
  have hstable : (prefixWord ++ tailWord_4944305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944305).length < 2 ^ (prefixWord ++ tailWord_4944305).sum := by decide
  have hdescent : baseEnd_4944305 < baseStart_4944305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944345 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 4, 5]
def baseStart_4944345 : Nat := 118140960795 + 4944345 * 2 ^ 59
def prefixEnd_4944345 : Nat := 4983230072969 + 3 ^ 40 * 4944345 * 2
def baseEnd_4944345 : Nat := 846275168884854320382959

theorem tailTrace_4944345 : CollatzResearch.WordTrace tailWord_4944345 prefixEnd_4944345 846275168884854320382959 := by
  unfold tailWord_4944345
  simp only [CollatzResearch.WordTrace]
  refine ⟨180335077272489966742850489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120223384848326644495233659 180335077272489966742850489)
  ·
    refine ⟨135251307954367475057137867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180335077272489966742850489 135251307954367475057137867)
    ·
      refine ⟨202876961931551212585706801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135251307954367475057137867 202876961931551212585706801)
      ·
        refine ⟨152157721448663409439280101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202876961931551212585706801 152157721448663409439280101)
        ·
          refine ⟨28529572771624389269865019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152157721448663409439280101 28529572771624389269865019)
          ·
            refine ⟨42794359157436583904797529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28529572771624389269865019 42794359157436583904797529)
            ·
              refine ⟨32095769368077437928598147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42794359157436583904797529 32095769368077437928598147)
              ·
                refine ⟨48143654052116156892897221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32095769368077437928598147 48143654052116156892897221)
                ·
                  refine ⟨9026935134771779417418229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48143654052116156892897221 9026935134771779417418229)
                  ·
                    refine ⟨846275168884854320382959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9026935134771779417418229 846275168884854320382959)
                    ·
                      rfl

theorem cell23_4944345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 5].length) (baseStart_4944345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944345 prefixEnd_4944345 := by exact prefixLift 4944345
  have htrace : WordTrace (prefixWord ++ tailWord_4944345) baseStart_4944345 baseEnd_4944345 := by
    simpa [prefixWord, tailWord_4944345, baseEnd_4944345] using wordTrace_append hprefix tailTrace_4944345
  have hstable : (prefixWord ++ tailWord_4944345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944345).length < 2 ^ (prefixWord ++ tailWord_4944345).sum := by decide
  have hdescent : baseEnd_4944345 < baseStart_4944345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944405 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 8]
def baseStart_4944405 : Nat := 118140960795 + 4944405 * 2 ^ 59
def prefixEnd_4944405 : Nat := 4983230072969 + 3 ^ 40 * 4944405 * 2
def baseEnd_4944405 : Nat := 282095146165981414044289

theorem tailTrace_4944405 : CollatzResearch.WordTrace tailWord_4944405 prefixEnd_4944405 282095146165981414044289 := by
  unfold tailWord_4944405
  simp only [CollatzResearch.WordTrace]
  refine ⟨180337265652272596990034669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120224843768181731326689779 180337265652272596990034669)
  ·
    refine ⟨67626474619602223871263001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180337265652272596990034669 67626474619602223871263001)
    ·
      refine ⟨50719855964701667903447251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67626474619602223871263001 50719855964701667903447251)
      ·
        refine ⟨76079783947052501855170877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50719855964701667903447251 76079783947052501855170877)
        ·
          refine ⟨28529918980144688195689079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76079783947052501855170877 28529918980144688195689079)
          ·
            refine ⟨42794878470217032293533619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28529918980144688195689079 42794878470217032293533619)
            ·
              refine ⟨64192317705325548440300429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42794878470217032293533619 64192317705325548440300429)
              ·
                refine ⟨24072119139497080665112661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64192317705325548440300429 24072119139497080665112661)
                ·
                  refine ⟨282095146165981414044289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24072119139497080665112661 282095146165981414044289)
                  ·
                    rfl

theorem cell23_4944405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 8].length) (baseStart_4944405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944405 prefixEnd_4944405 := by exact prefixLift 4944405
  have htrace : WordTrace (prefixWord ++ tailWord_4944405) baseStart_4944405 baseEnd_4944405 := by
    simpa [prefixWord, tailWord_4944405, baseEnd_4944405] using wordTrace_append hprefix tailTrace_4944405
  have hstable : (prefixWord ++ tailWord_4944405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944405).length < 2 ^ (prefixWord ++ tailWord_4944405).sum := by decide
  have hdescent : baseEnd_4944405 < baseStart_4944405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944459 : List Nat := [1, 1, 1, 1, 3, 1, 6, 2, 2, 3, 2]
def baseStart_4944459 : Nat := 118140960795 + 4944459 * 2 ^ 59
def prefixEnd_4944459 : Nat := 4983230072969 + 3 ^ 40 * 4944459 * 2
def baseEnd_4944459 : Nat := 2538884043449175515123353

theorem tailTrace_4944459 : CollatzResearch.WordTrace tailWord_4944459 prefixEnd_4944459 2538884043449175515123353 := by
  unfold tailWord_4944459
  simp only [CollatzResearch.WordTrace]
  refine ⟨180339235194076964212500431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120226156796051309475000287 180339235194076964212500431)
  ·
    refine ⟨270508852791115446318750647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180339235194076964212500431 270508852791115446318750647)
    ·
      refine ⟨405763279186673169478125971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270508852791115446318750647 405763279186673169478125971)
      ·
        refine ⟨608644918780009754217188957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405763279186673169478125971 608644918780009754217188957)
        ·
          refine ⟨228241844542503657831445859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 608644918780009754217188957 228241844542503657831445859)
          ·
            refine ⟨342362766813755486747168789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228241844542503657831445859 342362766813755486747168789)
            ·
              refine ⟨16048254694394788441273537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 342362766813755486747168789 16048254694394788441273537)
              ·
                refine ⟨12036191020796091330955153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16048254694394788441273537 12036191020796091330955153)
                ·
                  refine ⟨9027143265597068498216365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12036191020796091330955153 9027143265597068498216365)
                  ·
                    refine ⟨3385178724598900686831137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9027143265597068498216365 3385178724598900686831137)
                    ·
                      refine ⟨2538884043449175515123353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3385178724598900686831137 2538884043449175515123353)
                      ·
                        rfl

theorem cell23_4944459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 3, 2].length) (baseStart_4944459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944459 prefixEnd_4944459 := by exact prefixLift 4944459
  have htrace : WordTrace (prefixWord ++ tailWord_4944459) baseStart_4944459 baseEnd_4944459 := by
    simpa [prefixWord, tailWord_4944459, baseEnd_4944459] using wordTrace_append hprefix tailTrace_4944459
  have hstable : (prefixWord ++ tailWord_4944459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944459).length < 2 ^ (prefixWord ++ tailWord_4944459).sum := by decide
  have hdescent : baseEnd_4944459 < baseStart_4944459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944472 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 3, 1, 4]
def baseStart_4944472 : Nat := 118140960795 + 4944472 * 2 ^ 59
def prefixEnd_4944472 : Nat := 4983230072969 + 3 ^ 40 * 4944472 * 2
def baseEnd_4944472 : Nat := 2538890718697683964260793

theorem tailTrace_4944472 : CollatzResearch.WordTrace tailWord_4944472 prefixEnd_4944472 2538890718697683964260793 := by
  unfold tailWord_4944472
  simp only [CollatzResearch.WordTrace]
  refine ⟨90169854671514933716361835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120226472895353244955149113 90169854671514933716361835)
  ·
    refine ⟨135254782007272400574542753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90169854671514933716361835 135254782007272400574542753)
    ·
      refine ⟨101441086505454300430907065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135254782007272400574542753 101441086505454300430907065)
      ·
        refine ⟨76080814879090725323180299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101441086505454300430907065 76080814879090725323180299)
        ·
          refine ⟨114121222318636087984770449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76080814879090725323180299 114121222318636087984770449)
          ·
            refine ⟨85590916738977065988577837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114121222318636087984770449 85590916738977065988577837)
            ·
              refine ⟨32096593777116399745716689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85590916738977065988577837 32096593777116399745716689)
              ·
                refine ⟨24072445332837299809287517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32096593777116399745716689 24072445332837299809287517)
                ·
                  refine ⟨9027166999813987428482819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24072445332837299809287517 9027166999813987428482819)
                  ·
                    refine ⟨13540750499720981142724229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9027166999813987428482819 13540750499720981142724229)
                    ·
                      refine ⟨2538890718697683964260793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13540750499720981142724229 2538890718697683964260793)
                      ·
                        rfl

theorem cell23_4944472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_4944472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944472 prefixEnd_4944472 := by exact prefixLift 4944472
  have htrace : WordTrace (prefixWord ++ tailWord_4944472) baseStart_4944472 baseEnd_4944472 := by
    simpa [prefixWord, tailWord_4944472, baseEnd_4944472] using wordTrace_append hprefix tailTrace_4944472
  have hstable : (prefixWord ++ tailWord_4944472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944472).length < 2 ^ (prefixWord ++ tailWord_4944472).sum := by decide
  have hdescent : baseEnd_4944472 < baseStart_4944472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944493 : List Nat := [1, 5, 1, 1, 3, 3, 1, 1, 2, 3, 2]
def baseStart_4944493 : Nat := 118140960795 + 4944493 * 2 ^ 59
def prefixEnd_4944493 : Nat := 4983230072969 + 3 ^ 40 * 4944493 * 2
def baseEnd_4944493 : Nat := 2538901501791428382098197

theorem tailTrace_4944493 : CollatzResearch.WordTrace tailWord_4944493 prefixEnd_4944493 2538901501791428382098197 := by
  unfold tailWord_4944493
  simp only [CollatzResearch.WordTrace]
  refine ⟨180340475275953788019238133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120226983517302525346158755 180340475275953788019238133)
  ·
    refine ⟨16906919557120667626803575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 180340475275953788019238133 16906919557120667626803575)
    ·
      refine ⟨25360379335681001440205363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16906919557120667626803575 25360379335681001440205363)
      ·
        refine ⟨38040569003521502160308045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25360379335681001440205363 38040569003521502160308045)
        ·
          refine ⟨14265213376320563310115517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38040569003521502160308045 14265213376320563310115517)
          ·
            refine ⟨5349455016120211241293319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14265213376320563310115517 5349455016120211241293319)
            ·
              refine ⟨8024182524180316861939979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5349455016120211241293319 8024182524180316861939979)
              ·
                refine ⟨12036273786270475292909969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8024182524180316861939979 12036273786270475292909969)
                ·
                  refine ⟨9027205339702856469682477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12036273786270475292909969 9027205339702856469682477)
                  ·
                    refine ⟨3385202002388571176130929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9027205339702856469682477 3385202002388571176130929)
                    ·
                      refine ⟨2538901501791428382098197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3385202002388571176130929 2538901501791428382098197)
                      ·
                        rfl

theorem cell23_4944493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_4944493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944493 prefixEnd_4944493 := by exact prefixLift 4944493
  have htrace : WordTrace (prefixWord ++ tailWord_4944493) baseStart_4944493 baseEnd_4944493 := by
    simpa [prefixWord, tailWord_4944493, baseEnd_4944493] using wordTrace_append hprefix tailTrace_4944493
  have hstable : (prefixWord ++ tailWord_4944493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944493).length < 2 ^ (prefixWord ++ tailWord_4944493).sum := by decide
  have hdescent : baseEnd_4944493 < baseStart_4944493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944495 : List Nat := [1, 1, 2, 1, 3, 2, 2, 11]
def baseStart_4944495 : Nat := 118140960795 + 4944495 * 2 ^ 59
def prefixEnd_4944495 : Nat := 4983230072969 + 3 ^ 40 * 4944495 * 2
def baseEnd_4944495 : Nat := 94033426990842124973081

theorem tailTrace_4944495 : CollatzResearch.WordTrace tailWord_4944495 prefixEnd_4944495 94033426990842124973081 := by
  unfold tailWord_4944495
  simp only [CollatzResearch.WordTrace]
  refine ⟨180340548221946542360810939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120227032147964361573873959 180340548221946542360810939)
  ·
    refine ⟨270510822332919813541216409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180340548221946542360810939 270510822332919813541216409)
    ·
      refine ⟨202883116749689860155912307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270510822332919813541216409 202883116749689860155912307)
      ·
        refine ⟨304324675124534790233868461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202883116749689860155912307 304324675124534790233868461)
        ·
          refine ⟨114121753171700546337700673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 304324675124534790233868461 114121753171700546337700673)
          ·
            refine ⟨85591314878775409753275505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114121753171700546337700673 85591314878775409753275505)
            ·
              refine ⟨64193486159081557314956629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85591314878775409753275505 64193486159081557314956629)
              ·
                refine ⟨94033426990842124973081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 64193486159081557314956629 94033426990842124973081)
                ·
                  rfl

theorem cell23_4944495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 11].length) (baseStart_4944495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944495 prefixEnd_4944495 := by exact prefixLift 4944495
  have htrace : WordTrace (prefixWord ++ tailWord_4944495) baseStart_4944495 baseEnd_4944495 := by
    simpa [prefixWord, tailWord_4944495, baseEnd_4944495] using wordTrace_append hprefix tailTrace_4944495
  have hstable : (prefixWord ++ tailWord_4944495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944495).length < 2 ^ (prefixWord ++ tailWord_4944495).sum := by decide
  have hdescent : baseEnd_4944495 < baseStart_4944495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944516 : List Nat := [2, 3, 2, 1, 3, 1, 3, 2, 2, 4]
def baseStart_4944516 : Nat := 118140960795 + 4944516 * 2 ^ 59
def prefixEnd_4944516 : Nat := 4983230072969 + 3 ^ 40 * 4944516 * 2
def baseEnd_4944516 : Nat := 846304437282160597370197

theorem tailTrace_4944516 : CollatzResearch.WordTrace tailWord_4944516 prefixEnd_4944516 846304437282160597370197 := by
  unfold tailWord_4944516
  simp only [CollatzResearch.WordTrace]
  refine ⟨90170657077435231473662701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120227542769913641964883601 90170657077435231473662701)
  ·
    refine ⟨33813996404038211802623513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90170657077435231473662701 33813996404038211802623513)
    ·
      refine ⟨25360497303028658851967635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33813996404038211802623513 25360497303028658851967635)
      ·
        refine ⟨38040745954542988277951453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25360497303028658851967635 38040745954542988277951453)
        ·
          refine ⟨14265279732953620604231795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38040745954542988277951453 14265279732953620604231795)
          ·
            refine ⟨21397919599430430906347693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14265279732953620604231795 21397919599430430906347693)
            ·
              refine ⟨8024219849786411589880385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21397919599430430906347693 8024219849786411589880385)
              ·
                refine ⟨6018164887339808692410289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8024219849786411589880385 6018164887339808692410289)
                ·
                  refine ⟨4513623665504856519307717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6018164887339808692410289 4513623665504856519307717)
                  ·
                    refine ⟨846304437282160597370197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4513623665504856519307717 846304437282160597370197)
                    ·
                      rfl

theorem cell23_4944516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_4944516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944516 prefixEnd_4944516 := by exact prefixLift 4944516
  have htrace : WordTrace (prefixWord ++ tailWord_4944516) baseStart_4944516 baseEnd_4944516 := by
    simpa [prefixWord, tailWord_4944516, baseEnd_4944516] using wordTrace_append hprefix tailTrace_4944516
  have hstable : (prefixWord ++ tailWord_4944516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944516).length < 2 ^ (prefixWord ++ tailWord_4944516).sum := by decide
  have hdescent : baseEnd_4944516 < baseStart_4944516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944557 : List Nat := [1, 5, 2, 1, 1, 4, 1, 3, 1, 2, 2]
def baseStart_4944557 : Nat := 118140960795 + 4944557 * 2 ^ 59
def prefixEnd_4944557 : Nat := 4983230072969 + 3 ^ 40 * 4944557 * 2
def baseEnd_4944557 : Nat := 2538934364553316131697903

theorem tailTrace_4944557 : CollatzResearch.WordTrace tailWord_4944557 prefixEnd_4944557 2538934364553316131697903 := by
  unfold tailWord_4944557
  simp only [CollatzResearch.WordTrace]
  refine ⟨180342809547721926949567925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120228539698481284633045283 180342809547721926949567925)
  ·
    refine ⟨16907138395098930651521993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 180342809547721926949567925 16907138395098930651521993)
    ·
      refine ⟨12680353796324197988641495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16907138395098930651521993 12680353796324197988641495)
      ·
        refine ⟨19020530694486296982962243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12680353796324197988641495 19020530694486296982962243)
        ·
          refine ⟨28530796041729445474443365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19020530694486296982962243 28530796041729445474443365)
          ·
            refine ⟨5349524257824271026458131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28530796041729445474443365 5349524257824271026458131)
            ·
              refine ⟨8024286386736406539687197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5349524257824271026458131 8024286386736406539687197)
              ·
                refine ⟨3009107395026152452382699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8024286386736406539687197 3009107395026152452382699)
                ·
                  refine ⟨4513661092539228678574049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3009107395026152452382699 4513661092539228678574049)
                  ·
                    refine ⟨3385245819404421508930537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4513661092539228678574049 3385245819404421508930537)
                    ·
                      refine ⟨2538934364553316131697903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3385245819404421508930537 2538934364553316131697903)
                      ·
                        rfl

theorem cell23_4944557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_4944557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944557 prefixEnd_4944557 := by exact prefixLift 4944557
  have htrace : WordTrace (prefixWord ++ tailWord_4944557) baseStart_4944557 baseEnd_4944557 := by
    simpa [prefixWord, tailWord_4944557, baseEnd_4944557] using wordTrace_append hprefix tailTrace_4944557
  have hstable : (prefixWord ++ tailWord_4944557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944557).length < 2 ^ (prefixWord ++ tailWord_4944557).sum := by decide
  have hdescent : baseEnd_4944557 < baseStart_4944557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944562 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_4944562 : Nat := 118140960795 + 4944562 * 2 ^ 59
def prefixEnd_4944562 : Nat := 4983230072969 + 3 ^ 40 * 4944562 * 2
def baseEnd_4944562 : Nat := 2538936931956588612135379

theorem tailTrace_4944562 : CollatzResearch.WordTrace tailWord_4944562 prefixEnd_4944562 2538936931956588612135379 := by
  unfold tailWord_4944562
  simp only [CollatzResearch.WordTrace]
  refine ⟨45085747978175953200874985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120228661275135875202333293 45085747978175953200874985)
  ·
    refine ⟨33814310983631964900656239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45085747978175953200874985 33814310983631964900656239)
    ·
      refine ⟨50721466475447947350984359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33814310983631964900656239 50721466475447947350984359)
      ·
        refine ⟨76082199713171921026476539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50721466475447947350984359 76082199713171921026476539)
        ·
          refine ⟨114123299569757881539714809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76082199713171921026476539 114123299569757881539714809)
          ·
            refine ⟨85592474677318411154786107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114123299569757881539714809 85592474677318411154786107)
            ·
              refine ⟨128388712015977616732179161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85592474677318411154786107 128388712015977616732179161)
              ·
                refine ⟨96291534011983212549134371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128388712015977616732179161 96291534011983212549134371)
                ·
                  refine ⟨144437301017974818823701557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96291534011983212549134371 144437301017974818823701557)
                  ·
                    refine ⟨13540996970435139264722021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 144437301017974818823701557 13540996970435139264722021)
                    ·
                      refine ⟨2538936931956588612135379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13540996970435139264722021 2538936931956588612135379)
                      ·
                        rfl

theorem cell23_4944562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_4944562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944562 prefixEnd_4944562 := by exact prefixLift 4944562
  have htrace : WordTrace (prefixWord ++ tailWord_4944562) baseStart_4944562 baseEnd_4944562 := by
    simpa [prefixWord, tailWord_4944562, baseEnd_4944562] using wordTrace_append hprefix tailTrace_4944562
  have hstable : (prefixWord ++ tailWord_4944562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944562).length < 2 ^ (prefixWord ++ tailWord_4944562).sum := by decide
  have hdescent : baseEnd_4944562 < baseStart_4944562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944590 : List Nat := [4, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3]
def baseStart_4944590 : Nat := 118140960795 + 4944590 * 2 ^ 59
def prefixEnd_4944590 : Nat := 4983230072969 + 3 ^ 40 * 4944590 * 2
def baseEnd_4944590 : Nat := 2538951309414914502585251

theorem tailTrace_4944590 : CollatzResearch.WordTrace tailWord_4944590 prefixEnd_4944590 2538951309414914502585251 := by
  unfold tailWord_4944590
  simp only [CollatzResearch.WordTrace]
  refine ⟨22543001644575296698189903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120229342104401582390346149 22543001644575296698189903)
  ·
    refine ⟨33814502466862945047284855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22543001644575296698189903 33814502466862945047284855)
    ·
      refine ⟨50721753700294417570927283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33814502466862945047284855 50721753700294417570927283)
      ·
        refine ⟨76082630550441626356390925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50721753700294417570927283 76082630550441626356390925)
        ·
          refine ⟨28530986456415609883646597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76082630550441626356390925 28530986456415609883646597)
          ·
            refine ⟨5349559960577926853183737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28530986456415609883646597 5349559960577926853183737)
            ·
              refine ⟨4012169970433445139887803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5349559960577926853183737 4012169970433445139887803)
              ·
                refine ⟨6018254955650167709831705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4012169970433445139887803 6018254955650167709831705)
                ·
                  refine ⟨4513691216737625782373779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6018254955650167709831705 4513691216737625782373779)
                  ·
                    refine ⟨6770536825106438673560669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4513691216737625782373779 6770536825106438673560669)
                    ·
                      refine ⟨2538951309414914502585251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6770536825106438673560669 2538951309414914502585251)
                      ·
                        rfl

theorem cell23_4944590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_4944590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944590 prefixEnd_4944590 := by exact prefixLift 4944590
  have htrace : WordTrace (prefixWord ++ tailWord_4944590) baseStart_4944590 baseEnd_4944590 := by
    simpa [prefixWord, tailWord_4944590, baseEnd_4944590] using wordTrace_append hprefix tailTrace_4944590
  have hstable : (prefixWord ++ tailWord_4944590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944590).length < 2 ^ (prefixWord ++ tailWord_4944590).sum := by decide
  have hdescent : baseEnd_4944590 < baseStart_4944590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944592 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 4]
def baseStart_4944592 : Nat := 118140960795 + 4944592 * 2 ^ 59
def prefixEnd_4944592 : Nat := 4983230072969 + 3 ^ 40 * 4944592 * 2
def baseEnd_4944592 : Nat := 2538952336376223494760241

theorem tailTrace_4944592 : CollatzResearch.WordTrace tailWord_4944592 prefixEnd_4944592 2538952336376223494760241 := by
  unfold tailWord_4944592
  simp only [CollatzResearch.WordTrace]
  refine ⟨90172043051297563963546015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120229390735063418618061353 90172043051297563963546015)
  ·
    refine ⟨135258064576946345945319023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90172043051297563963546015 135258064576946345945319023)
    ·
      refine ⟨202887096865419518917978535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135258064576946345945319023 202887096865419518917978535)
      ·
        refine ⟨304330645298129278376967803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202887096865419518917978535 304330645298129278376967803)
        ·
          refine ⟨456495967947193917565451705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304330645298129278376967803 456495967947193917565451705)
          ·
            refine ⟨342371975960395438174088779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 456495967947193917565451705 342371975960395438174088779)
            ·
              refine ⟨513557963940593157261133169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342371975960395438174088779 513557963940593157261133169)
              ·
                refine ⟨385168472955444867945849877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513557963940593157261133169 385168472955444867945849877)
                ·
                  refine ⟨18054772169786478184961713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 385168472955444867945849877 18054772169786478184961713)
                  ·
                    refine ⟨13541079127339858638721285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18054772169786478184961713 13541079127339858638721285)
                    ·
                      refine ⟨2538952336376223494760241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13541079127339858638721285 2538952336376223494760241)
                      ·
                        rfl

theorem cell23_4944592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 4].length) (baseStart_4944592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944592 prefixEnd_4944592 := by exact prefixLift 4944592
  have htrace : WordTrace (prefixWord ++ tailWord_4944592) baseStart_4944592 baseEnd_4944592 := by
    simpa [prefixWord, tailWord_4944592, baseEnd_4944592] using wordTrace_append hprefix tailTrace_4944592
  have hstable : (prefixWord ++ tailWord_4944592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944592).length < 2 ^ (prefixWord ++ tailWord_4944592).sum := by decide
  have hdescent : baseEnd_4944592 < baseStart_4944592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944602 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 9]
def baseStart_4944602 : Nat := 118140960795 + 4944602 * 2 ^ 59
def prefixEnd_4944602 : Nat := 4983230072969 + 3 ^ 40 * 4944602 * 2
def baseEnd_4944602 : Nat := 282106385686974272848355

theorem tailTrace_4944602 : CollatzResearch.WordTrace tailWord_4944602 prefixEnd_4944602 282106385686974272848355 := by
  unfold tailWord_4944602
  simp only [CollatzResearch.WordTrace]
  refine ⟨45086112708139724908739015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120229633888372599756637373 45086112708139724908739015)
  ·
    refine ⟨67629169062209587363108523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45086112708139724908739015 67629169062209587363108523)
    ·
      refine ⟨101443753593314381044662785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67629169062209587363108523 101443753593314381044662785)
      ·
        refine ⟨76082815194985785783497089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101443753593314381044662785 76082815194985785783497089)
        ·
          refine ⟨57062111396239339337622817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76082815194985785783497089 57062111396239339337622817)
          ·
            refine ⟨42796583547179504503217113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57062111396239339337622817 42796583547179504503217113)
            ·
              refine ⟨32097437660384628377412835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42796583547179504503217113 32097437660384628377412835)
              ·
                refine ⟨48146156490576942566119253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32097437660384628377412835 48146156490576942566119253)
                ·
                  refine ⟨282106385686974272848355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48146156490576942566119253 282106385686974272848355)
                  ·
                    rfl

theorem cell23_4944602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 9].length) (baseStart_4944602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944602 prefixEnd_4944602 := by exact prefixLift 4944602
  have htrace : WordTrace (prefixWord ++ tailWord_4944602) baseStart_4944602 baseEnd_4944602 := by
    simpa [prefixWord, tailWord_4944602, baseEnd_4944602] using wordTrace_append hprefix tailTrace_4944602
  have hstable : (prefixWord ++ tailWord_4944602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944602).length < 2 ^ (prefixWord ++ tailWord_4944602).sum := by decide
  have hdescent : baseEnd_4944602 < baseStart_4944602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944619 : List Nat := [1, 1, 1, 1, 2, 4, 1, 7, 5]
def baseStart_4944619 : Nat := 118140960795 + 4944619 * 2 ^ 59
def prefixEnd_4944619 : Nat := 4983230072969 + 3 ^ 40 * 4944619 * 2
def baseEnd_4944619 : Nat := 282107355594877209902513

theorem tailTrace_4944619 : CollatzResearch.WordTrace tailWord_4944619 prefixEnd_4944619 282107355594877209902513 := by
  unfold tailWord_4944619
  simp only [CollatzResearch.WordTrace]
  refine ⟨180345070873497311538324911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120230047248998207692216607 180345070873497311538324911)
  ·
    refine ⟨270517606310245967307487367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180345070873497311538324911 270517606310245967307487367)
    ·
      refine ⟨405776409465368950961231051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270517606310245967307487367 405776409465368950961231051)
      ·
        refine ⟨608664614198053426441846577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405776409465368950961231051 608664614198053426441846577)
        ·
          refine ⟨456498460648540069831384933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 608664614198053426441846577 456498460648540069831384933)
          ·
            refine ⟨85593461371601263093384675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 456498460648540069831384933 85593461371601263093384675)
            ·
              refine ⟨128390192057401894640077013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85593461371601263093384675 128390192057401894640077013)
              ·
                refine ⟨3009145126345356905626805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 128390192057401894640077013 3009145126345356905626805)
                ·
                  refine ⟨282107355594877209902513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3009145126345356905626805 282107355594877209902513)
                  ·
                    rfl

theorem cell23_4944619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 5].length) (baseStart_4944619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944619 prefixEnd_4944619 := by exact prefixLift 4944619
  have htrace : WordTrace (prefixWord ++ tailWord_4944619) baseStart_4944619 baseEnd_4944619 := by
    simpa [prefixWord, tailWord_4944619, baseEnd_4944619] using wordTrace_append hprefix tailTrace_4944619
  have hstable : (prefixWord ++ tailWord_4944619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944619).length < 2 ^ (prefixWord ++ tailWord_4944619).sum := by decide
  have hdescent : baseEnd_4944619 < baseStart_4944619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944630 : List Nat := [5, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2]
def baseStart_4944630 : Nat := 118140960795 + 4944630 * 2 ^ 59
def prefixEnd_4944630 : Nat := 4983230072969 + 3 ^ 40 * 4944630 * 2
def baseEnd_4944630 : Nat := 2538971848641094346085067

theorem tailTrace_4944630 : CollatzResearch.WordTrace tailWord_4944630 prefixEnd_4944630 2538971848641094346085067 := by
  unfold tailWord_4944630
  simp only [CollatzResearch.WordTrace]
  refine ⟨11271592004778591276060959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120230314717638306944650229 11271592004778591276060959)
  ·
    refine ⟨16907388007167886914091439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11271592004778591276060959 16907388007167886914091439)
    ·
      refine ⟨25361082010751830371137159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16907388007167886914091439 25361082010751830371137159)
      ·
        refine ⟨38041623016127745556705739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25361082010751830371137159 38041623016127745556705739)
        ·
          refine ⟨57062434524191618335058609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38041623016127745556705739 57062434524191618335058609)
          ·
            refine ⟨42796825893143713751293957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57062434524191618335058609 42796825893143713751293957)
            ·
              refine ⟨8024404854964446328367617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42796825893143713751293957 8024404854964446328367617)
              ·
                refine ⟨6018303641223334746275713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8024404854964446328367617 6018303641223334746275713)
                ·
                  refine ⟨4513727730917501059706785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6018303641223334746275713 4513727730917501059706785)
                  ·
                    refine ⟨3385295798188125794780089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4513727730917501059706785 3385295798188125794780089)
                    ·
                      refine ⟨2538971848641094346085067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3385295798188125794780089 2538971848641094346085067)
                      ·
                        rfl

theorem cell23_4944630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_4944630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944630 prefixEnd_4944630 := by exact prefixLift 4944630
  have htrace : WordTrace (prefixWord ++ tailWord_4944630) baseStart_4944630 baseEnd_4944630 := by
    simpa [prefixWord, tailWord_4944630, baseEnd_4944630] using wordTrace_append hprefix tailTrace_4944630
  have hstable : (prefixWord ++ tailWord_4944630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944630).length < 2 ^ (prefixWord ++ tailWord_4944630).sum := by decide
  have hdescent : baseEnd_4944630 < baseStart_4944630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944636 : List Nat := [2, 2, 2, 1, 3, 3, 1, 4, 5]
def baseStart_4944636 : Nat := 118140960795 + 4944636 * 2 ^ 59
def prefixEnd_4944636 : Nat := 4983230072969 + 3 ^ 40 * 4944636 * 2
def baseEnd_4944636 : Nat := 282108325502780146956671

theorem tailTrace_4944636 : CollatzResearch.WordTrace tailWord_4944636 prefixEnd_4944636 282108325502780146956671 := by
  unfold tailWord_4944636
  simp only [CollatzResearch.WordTrace]
  refine ⟨90172845457217861720846881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120230460609623815627795841 90172845457217861720846881)
  ·
    refine ⟨67629634092913396290635161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90172845457217861720846881 67629634092913396290635161)
    ·
      refine ⟨50722225569685047217976371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67629634092913396290635161 50722225569685047217976371)
      ·
        refine ⟨76083338354527570826964557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50722225569685047217976371 76083338354527570826964557)
        ·
          refine ⟨28531251882947839060111709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76083338354527570826964557 28531251882947839060111709)
          ·
            refine ⟨10699219456105439647541891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28531251882947839060111709 10699219456105439647541891)
            ·
              refine ⟨16048829184158159471312837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10699219456105439647541891 16048829184158159471312837)
              ·
                refine ⟨3009155472029654900871157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16048829184158159471312837 3009155472029654900871157)
                ·
                  refine ⟨282108325502780146956671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3009155472029654900871157 282108325502780146956671)
                  ·
                    rfl

theorem cell23_4944636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 5].length) (baseStart_4944636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944636 prefixEnd_4944636 := by exact prefixLift 4944636
  have htrace : WordTrace (prefixWord ++ tailWord_4944636) baseStart_4944636 baseEnd_4944636 := by
    simpa [prefixWord, tailWord_4944636, baseEnd_4944636] using wordTrace_append hprefix tailTrace_4944636
  have hstable : (prefixWord ++ tailWord_4944636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944636).length < 2 ^ (prefixWord ++ tailWord_4944636).sum := by decide
  have hdescent : baseEnd_4944636 < baseStart_4944636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944696 : List Nat := [2, 1, 2, 1, 3, 2, 4, 1, 3, 4]
def baseStart_4944696 : Nat := 118140960795 + 4944696 * 2 ^ 59
def prefixEnd_4944696 : Nat := 4983230072969 + 3 ^ 40 * 4944696 * 2
def baseEnd_4944696 : Nat := 846335246121430362619921

theorem tailTrace_4944696 : CollatzResearch.WordTrace tailWord_4944696 prefixEnd_4944696 846335246121430362619921 := by
  unfold tailWord_4944696
  simp only [CollatzResearch.WordTrace]
  refine ⟨90173939647109176844438971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120231919529478902459251961 90173939647109176844438971)
  ·
    refine ⟨135260909470663765266658457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90173939647109176844438971 135260909470663765266658457)
    ·
      refine ⟨101445682102997823949993843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135260909470663765266658457 101445682102997823949993843)
      ·
        refine ⟨152168523154496735924990765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101445682102997823949993843 152168523154496735924990765)
        ·
          refine ⟨57063196182936275971871537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152168523154496735924990765 57063196182936275971871537)
          ·
            refine ⟨42797397137202206978903653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57063196182936275971871537 42797397137202206978903653)
            ·
              refine ⟨8024511963225413808544435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42797397137202206978903653 8024511963225413808544435)
              ·
                refine ⟨12036767944838120712816653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8024511963225413808544435 12036767944838120712816653)
                ·
                  refine ⟨4513787979314295267306245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12036767944838120712816653 4513787979314295267306245)
                  ·
                    refine ⟨846335246121430362619921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4513787979314295267306245 846335246121430362619921)
                    ·
                      rfl

theorem cell23_4944696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 3, 4].length) (baseStart_4944696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944696 prefixEnd_4944696 := by exact prefixLift 4944696
  have htrace : WordTrace (prefixWord ++ tailWord_4944696) baseStart_4944696 baseEnd_4944696 := by
    simpa [prefixWord, tailWord_4944696, baseEnd_4944696] using wordTrace_append hprefix tailTrace_4944696
  have hstable : (prefixWord ++ tailWord_4944696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944696).length < 2 ^ (prefixWord ++ tailWord_4944696).sum := by decide
  have hdescent : baseEnd_4944696 < baseStart_4944696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944730 : List Nat := [3, 1, 1, 2, 1, 6, 1, 3, 1, 4]
def baseStart_4944730 : Nat := 118140960795 + 4944730 * 2 ^ 59
def prefixEnd_4944730 : Nat := 4983230072969 + 3 ^ 40 * 4944730 * 2
def baseEnd_4944730 : Nat := 846341065568847984944869

theorem tailTrace_4944730 : CollatzResearch.WordTrace tailWord_4944730 prefixEnd_4944730 846341065568847984944869 := by
  unfold tailWord_4944730
  simp only [CollatzResearch.WordTrace]
  refine ⟨45087279844023794373903911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120232746250730118330410429 45087279844023794373903911)
  ·
    refine ⟨67630919766035691560855867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45087279844023794373903911 67630919766035691560855867)
    ·
      refine ⟨101446379649053537341283801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67630919766035691560855867 101446379649053537341283801)
      ·
        refine ⟨76084784736790153005962851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101446379649053537341283801 76084784736790153005962851)
        ·
          refine ⟨114127177105185229508944277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76084784736790153005962851 114127177105185229508944277)
          ·
            refine ⟨5349711426805557633231763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 114127177105185229508944277 5349711426805557633231763)
            ·
              refine ⟨8024567140208336449847645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5349711426805557633231763 8024567140208336449847645)
              ·
                refine ⟨3009212677578126168692867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8024567140208336449847645 3009212677578126168692867)
                ·
                  refine ⟨4513819016367189253039301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3009212677578126168692867 4513819016367189253039301)
                  ·
                    refine ⟨846341065568847984944869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4513819016367189253039301 846341065568847984944869)
                    ·
                      rfl

theorem cell23_4944730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 1, 4].length) (baseStart_4944730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944730 prefixEnd_4944730 := by exact prefixLift 4944730
  have htrace : WordTrace (prefixWord ++ tailWord_4944730) baseStart_4944730 baseEnd_4944730 := by
    simpa [prefixWord, tailWord_4944730, baseEnd_4944730] using wordTrace_append hprefix tailTrace_4944730
  have hstable : (prefixWord ++ tailWord_4944730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944730).length < 2 ^ (prefixWord ++ tailWord_4944730).sum := by decide
  have hdescent : baseEnd_4944730 < baseStart_4944730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944749 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_4944749 : Nat := 118140960795 + 4944749 * 2 ^ 59
def prefixEnd_4944749 : Nat := 4983230072969 + 3 ^ 40 * 4944749 * 2
def baseEnd_4944749 : Nat := 2539032952838979380497019

theorem tailTrace_4944749 : CollatzResearch.WordTrace tailWord_4944749 prefixEnd_4944749 2539032952838979380497019 := by
  unfold tailWord_4944749
  simp only [CollatzResearch.WordTrace]
  refine ⟨180349812363026343740557301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120233208242017562493704867 180349812363026343740557301)
  ·
    refine ⟨16907794909033719725677247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 180349812363026343740557301 16907794909033719725677247)
    ·
      refine ⟨25361692363550579588515871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16907794909033719725677247 25361692363550579588515871)
      ·
        refine ⟨38042538545325869382773807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25361692363550579588515871 38042538545325869382773807)
        ·
          refine ⟨57063807817988804074160711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38042538545325869382773807 57063807817988804074160711)
          ·
            refine ⟨85595711726983206111241067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57063807817988804074160711 85595711726983206111241067)
            ·
              refine ⟨128393567590474809166861601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85595711726983206111241067 128393567590474809166861601)
              ·
                refine ⟨96295175692856106875146201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128393567590474809166861601 96295175692856106875146201)
                ·
                  refine ⟨72221381769642080156359651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96295175692856106875146201 72221381769642080156359651)
                  ·
                    refine ⟨108332072654463120234539477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72221381769642080156359651 108332072654463120234539477)
                    ·
                      refine ⟨2539032952838979380497019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108332072654463120234539477 2539032952838979380497019)
                      ·
                        rfl

theorem cell23_4944749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_4944749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944749 prefixEnd_4944749 := by exact prefixLift 4944749
  have htrace : WordTrace (prefixWord ++ tailWord_4944749) baseStart_4944749 baseEnd_4944749 := by
    simpa [prefixWord, tailWord_4944749, baseEnd_4944749] using wordTrace_append hprefix tailTrace_4944749
  have hstable : (prefixWord ++ tailWord_4944749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944749).length < 2 ^ (prefixWord ++ tailWord_4944749).sum := by decide
  have hdescent : baseEnd_4944749 < baseStart_4944749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944753 : List Nat := [1, 2, 2, 2, 1, 4, 3, 1, 3, 1, 3]
def baseStart_4944753 : Nat := 118140960795 + 4944753 * 2 ^ 59
def prefixEnd_4944753 : Nat := 4983230072969 + 3 ^ 40 * 4944753 * 2
def baseEnd_4944753 : Nat := 2539035006761597364847001

theorem tailTrace_4944753 : CollatzResearch.WordTrace tailWord_4944753 prefixEnd_4944753 2539035006761597364847001 := by
  unfold tailWord_4944753
  simp only [CollatzResearch.WordTrace]
  refine ⟨180349958255011852423702913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120233305503341234949135275 180349958255011852423702913)
  ·
    refine ⟨135262468691258889317777185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180349958255011852423702913 135262468691258889317777185)
    ·
      refine ⟨101446851518444166988332889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135262468691258889317777185 101446851518444166988332889)
      ·
        refine ⟨76085138638833125241249667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101446851518444166988332889 76085138638833125241249667)
        ·
          refine ⟨114127707958249687861874501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76085138638833125241249667 114127707958249687861874501)
          ·
            refine ⟨21398945242171816474101469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114127707958249687861874501 21398945242171816474101469)
            ·
              refine ⟨8024604465814431177788051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21398945242171816474101469 8024604465814431177788051)
              ·
                refine ⟨12036906698721646766682077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8024604465814431177788051 12036906698721646766682077)
                ·
                  refine ⟨4513840012020617537505779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12036906698721646766682077 4513840012020617537505779)
                  ·
                    refine ⟨6770760018030926306258669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4513840012020617537505779 6770760018030926306258669)
                    ·
                      refine ⟨2539035006761597364847001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6770760018030926306258669 2539035006761597364847001)
                      ·
                        rfl

theorem cell23_4944753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_4944753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944753 prefixEnd_4944753 := by exact prefixLift 4944753
  have htrace : WordTrace (prefixWord ++ tailWord_4944753) baseStart_4944753 baseEnd_4944753 := by
    simpa [prefixWord, tailWord_4944753, baseEnd_4944753] using wordTrace_append hprefix tailTrace_4944753
  have hstable : (prefixWord ++ tailWord_4944753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944753).length < 2 ^ (prefixWord ++ tailWord_4944753).sum := by decide
  have hdescent : baseEnd_4944753 < baseStart_4944753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944773 : List Nat := [1, 3, 1, 1, 3, 5, 1, 2, 1, 5]
def baseStart_4944773 : Nat := 118140960795 + 4944773 * 2 ^ 59
def prefixEnd_4944773 : Nat := 4983230072969 + 3 ^ 40 * 4944773 * 2
def baseEnd_4944773 : Nat := 846348425458229095532303

theorem tailTrace_4944773 : CollatzResearch.WordTrace tailWord_4944773 prefixEnd_4944773 846348425458229095532303 := by
  unfold tailWord_4944773
  simp only [CollatzResearch.WordTrace]
  refine ⟨180350687714939395839430973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120233791809959597226287315 180350687714939395839430973)
  ·
    refine ⟨67631507893102273439786615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180350687714939395839430973 67631507893102273439786615)
    ·
      refine ⟨101447261839653410159679923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67631507893102273439786615 101447261839653410159679923)
      ·
        refine ⟨152170892759480115239519885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101447261839653410159679923 152170892759480115239519885)
        ·
          refine ⟨57064084784805043214819957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152170892759480115239519885 57064084784805043214819957)
          ·
            refine ⟨5349757948575472801389371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57064084784805043214819957 5349757948575472801389371)
            ·
              refine ⟨8024636922863209202084057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5349757948575472801389371 8024636922863209202084057)
              ·
                refine ⟨6018477692147406901563043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8024636922863209202084057 6018477692147406901563043)
                ·
                  refine ⟨9027716538221110352344565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6018477692147406901563043 9027716538221110352344565)
                  ·
                    refine ⟨846348425458229095532303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9027716538221110352344565 846348425458229095532303)
                    ·
                      rfl

theorem cell23_4944773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 5].length) (baseStart_4944773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944773 prefixEnd_4944773 := by exact prefixLift 4944773
  have htrace : WordTrace (prefixWord ++ tailWord_4944773) baseStart_4944773 baseEnd_4944773 := by
    simpa [prefixWord, tailWord_4944773, baseEnd_4944773] using wordTrace_append hprefix tailTrace_4944773
  have hstable : (prefixWord ++ tailWord_4944773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944773).length < 2 ^ (prefixWord ++ tailWord_4944773).sum := by decide
  have hdescent : baseEnd_4944773 < baseStart_4944773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944779 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 5]
def baseStart_4944779 : Nat := 118140960795 + 4944779 * 2 ^ 59
def prefixEnd_4944779 : Nat := 4983230072969 + 3 ^ 40 * 4944779 * 2
def baseEnd_4944779 : Nat := 2539048357258614263121881

theorem tailTrace_4944779 : CollatzResearch.WordTrace tailWord_4944779 prefixEnd_4944779 2539048357258614263121881 := by
  unfold tailWord_4944779
  simp only [CollatzResearch.WordTrace]
  refine ⟨180350906552917658864149391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120233937701945105909432927 180350906552917658864149391)
  ·
    refine ⟨270526359829376488296224087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180350906552917658864149391 270526359829376488296224087)
    ·
      refine ⟨405789539744064732444336131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270526359829376488296224087 405789539744064732444336131)
      ·
        refine ⟨608684309616097098666504197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405789539744064732444336131 608684309616097098666504197)
        ·
          refine ⟨114128308053018205999969537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 608684309616097098666504197 114128308053018205999969537)
          ·
            refine ⟨85596231039763654499977153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114128308053018205999969537 85596231039763654499977153)
            ·
              refine ⟨64197173279822740874982865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85596231039763654499977153 64197173279822740874982865)
              ·
                refine ⟨48147879959867055656237149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64197173279822740874982865 48147879959867055656237149)
                ·
                  refine ⟨18055454984950145871088931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48147879959867055656237149 18055454984950145871088931)
                  ·
                    refine ⟨27083182477425218806633397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18055454984950145871088931 27083182477425218806633397)
                    ·
                      refine ⟨2539048357258614263121881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27083182477425218806633397 2539048357258614263121881)
                      ·
                        rfl

theorem cell23_4944779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 5].length) (baseStart_4944779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944779 prefixEnd_4944779 := by exact prefixLift 4944779
  have htrace : WordTrace (prefixWord ++ tailWord_4944779) baseStart_4944779 baseEnd_4944779 := by
    simpa [prefixWord, tailWord_4944779, baseEnd_4944779] using wordTrace_append hprefix tailTrace_4944779
  have hstable : (prefixWord ++ tailWord_4944779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944779).length < 2 ^ (prefixWord ++ tailWord_4944779).sum := by decide
  have hdescent : baseEnd_4944779 < baseStart_4944779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944799 : List Nat := [1, 1, 2, 5, 2, 12]
def baseStart_4944799 : Nat := 118140960795 + 4944799 * 2 ^ 59
def prefixEnd_4944799 : Nat := 4983230072969 + 3 ^ 40 * 4944799 * 2
def baseEnd_4944799 : Nat := 10448800933628412283423

theorem tailTrace_4944799 : CollatzResearch.WordTrace tailWord_4944799 prefixEnd_4944799 10448800933628412283423 := by
  unfold tailWord_4944799
  simp only [CollatzResearch.WordTrace]
  refine ⟨180351636012845202279877451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120234424008563468186584967 180351636012845202279877451)
  ·
    refine ⟨270527454019267803419816177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180351636012845202279877451 270527454019267803419816177)
    ·
      refine ⟨202895590514450852564862133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270527454019267803419816177 202895590514450852564862133)
      ·
        refine ⟨19021461610729767427955825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 202895590514450852564862133 19021461610729767427955825)
        ·
          refine ⟨14266096208047325570966869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19021461610729767427955825 14266096208047325570966869)
          ·
            refine ⟨10448800933628412283423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 14266096208047325570966869 10448800933628412283423)
            ·
              rfl

theorem cell23_4944799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 12].length) (baseStart_4944799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944799 prefixEnd_4944799 := by exact prefixLift 4944799
  have htrace : WordTrace (prefixWord ++ tailWord_4944799) baseStart_4944799 baseEnd_4944799 := by
    simpa [prefixWord, tailWord_4944799, baseEnd_4944799] using wordTrace_append hprefix tailTrace_4944799
  have hstable : (prefixWord ++ tailWord_4944799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944799).length < 2 ^ (prefixWord ++ tailWord_4944799).sum := by decide
  have hdescent : baseEnd_4944799 < baseStart_4944799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944820 : List Nat := [2, 5, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_4944820 : Nat := 118140960795 + 4944820 * 2 ^ 59
def prefixEnd_4944820 : Nat := 4983230072969 + 3 ^ 40 * 4944820 * 2
def baseEnd_4944820 : Nat := 846356469988482867569731

theorem tailTrace_4944820 : CollatzResearch.WordTrace tailWord_4944820 prefixEnd_4944820 846356469988482867569731 := by
  unfold tailWord_4944820
  simp only [CollatzResearch.WordTrace]
  refine ⟨90176200972884561433195957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120234934630512748577594609 90176200972884561433195957)
  ·
    refine ⟨8454018841207927634362121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90176200972884561433195957 8454018841207927634362121)
    ·
      refine ⟨6340514130905945725771591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8454018841207927634362121 6340514130905945725771591)
      ·
        refine ⟨9510771196358918588657387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6340514130905945725771591 9510771196358918588657387)
        ·
          refine ⟨14266156794538377882986081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9510771196358918588657387 14266156794538377882986081)
          ·
            refine ⟨10699617595903783412239561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14266156794538377882986081 10699617595903783412239561)
            ·
              refine ⟨8024713196927837559179671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10699617595903783412239561 8024713196927837559179671)
              ·
                refine ⟨12037069795391756338769507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8024713196927837559179671 12037069795391756338769507)
                ·
                  refine ⟨18055604693087634508154261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12037069795391756338769507 18055604693087634508154261)
                  ·
                    refine ⟨846356469988482867569731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18055604693087634508154261 846356469988482867569731)
                    ·
                      rfl

theorem cell23_4944820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_4944820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944820 prefixEnd_4944820 := by exact prefixLift 4944820
  have htrace : WordTrace (prefixWord ++ tailWord_4944820) baseStart_4944820 baseEnd_4944820 := by
    simpa [prefixWord, tailWord_4944820, baseEnd_4944820] using wordTrace_append hprefix tailTrace_4944820
  have hstable : (prefixWord ++ tailWord_4944820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944820).length < 2 ^ (prefixWord ++ tailWord_4944820).sum := by decide
  have hdescent : baseEnd_4944820 < baseStart_4944820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944946 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_4944946 : Nat := 118140960795 + 4944946 * 2 ^ 59
def prefixEnd_4944946 : Nat := 4983230072969 + 3 ^ 40 * 4944946 * 2
def baseEnd_4944946 : Nat := 2539134108527915109733613

theorem tailTrace_4944946 : CollatzResearch.WordTrace tailWord_4944946 prefixEnd_4944946 2539134108527915109733613 := by
  unfold tailWord_4944946
  simp only [CollatzResearch.WordTrace]
  refine ⟨45089249385828161596369673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120237998362208430923652461 45089249385828161596369673)
  ·
    refine ⟨33816937039371121197277255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45089249385828161596369673 33816937039371121197277255)
    ·
      refine ⟨50725405559056681795915883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33816937039371121197277255 50725405559056681795915883)
      ·
        refine ⟨76088108338585022693873825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50725405559056681795915883 76088108338585022693873825)
        ·
          refine ⟨57066081253938767020405369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76088108338585022693873825 57066081253938767020405369)
          ·
            refine ⟨42799560940454075265304027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57066081253938767020405369 42799560940454075265304027)
            ·
              refine ⟨64199341410681112897956041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42799560940454075265304027 64199341410681112897956041)
              ·
                refine ⟨48149506058010834673467031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64199341410681112897956041 48149506058010834673467031)
                ·
                  refine ⟨72224259087016252010200547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48149506058010834673467031 72224259087016252010200547)
                  ·
                    refine ⟨108336388630524378015300821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72224259087016252010200547 108336388630524378015300821)
                    ·
                      refine ⟨2539134108527915109733613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108336388630524378015300821 2539134108527915109733613)
                      ·
                        rfl

theorem cell23_4944946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_4944946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944946 prefixEnd_4944946 := by exact prefixLift 4944946
  have htrace : WordTrace (prefixWord ++ tailWord_4944946) baseStart_4944946 baseEnd_4944946 := by
    simpa [prefixWord, tailWord_4944946, baseEnd_4944946] using wordTrace_append hprefix tailTrace_4944946
  have hstable : (prefixWord ++ tailWord_4944946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944946).length < 2 ^ (prefixWord ++ tailWord_4944946).sum := by decide
  have hdescent : baseEnd_4944946 < baseStart_4944946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944953 : List Nat := [1, 2, 1, 5, 2, 1, 1, 3, 2, 5]
def baseStart_4944953 : Nat := 118140960795 + 4944953 * 2 ^ 59
def prefixEnd_4944953 : Nat := 4983230072969 + 3 ^ 40 * 4944953 * 2
def baseEnd_4944953 : Nat := 846379234297498860782027

theorem tailTrace_4944953 : CollatzResearch.WordTrace tailWord_4944953 prefixEnd_4944953 846379234297498860782027 := by
  unfold tailWord_4944953
  simp only [CollatzResearch.WordTrace]
  refine ⟨180357252854287286580983513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120238168569524857720655675 180357252854287286580983513)
  ·
    refine ⟨135267939640715464935737635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180357252854287286580983513 135267939640715464935737635)
    ·
      refine ⟨202901909461073197403606453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135267939640715464935737635 202901909461073197403606453)
      ·
        refine ⟨19022054011975612256588105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 202901909461073197403606453 19022054011975612256588105)
        ·
          refine ⟨14266540508981709192441079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19022054011975612256588105 14266540508981709192441079)
          ·
            refine ⟨21399810763472563788661619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14266540508981709192441079 21399810763472563788661619)
            ·
              refine ⟨32099716145208845682992429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21399810763472563788661619 32099716145208845682992429)
              ·
                refine ⟨12037393554453317131122161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32099716145208845682992429 12037393554453317131122161)
                ·
                  refine ⟨9028045165839987848341621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12037393554453317131122161 9028045165839987848341621)
                  ·
                    refine ⟨846379234297498860782027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9028045165839987848341621 846379234297498860782027)
                    ·
                      rfl

theorem cell23_4944953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 5].length) (baseStart_4944953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944953 prefixEnd_4944953 := by exact prefixLift 4944953
  have htrace : WordTrace (prefixWord ++ tailWord_4944953) baseStart_4944953 baseEnd_4944953 := by
    simpa [prefixWord, tailWord_4944953, baseEnd_4944953] using wordTrace_append hprefix tailTrace_4944953
  have hstable : (prefixWord ++ tailWord_4944953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944953).length < 2 ^ (prefixWord ++ tailWord_4944953).sum := by decide
  have hdescent : baseEnd_4944953 < baseStart_4944953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944983 : List Nat := [1, 1, 3, 2, 2, 1, 1, 5, 3, 4]
def baseStart_4944983 : Nat := 118140960795 + 4944983 * 2 ^ 59
def prefixEnd_4944983 : Nat := 4983230072969 + 3 ^ 40 * 4944983 * 2
def baseEnd_4944983 : Nat := 846384369104043821656981

theorem tailTrace_4944983 : CollatzResearch.WordTrace tailWord_4944983 prefixEnd_4944983 846384369104043821656981 := by
  unfold tailWord_4944983
  simp only [CollatzResearch.WordTrace]
  refine ⟨180358347044178601704575603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120238898029452401136383735 180358347044178601704575603)
  ·
    refine ⟨270537520566267902556863405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180358347044178601704575603 270537520566267902556863405)
    ·
      refine ⟨101451570212350463458823777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270537520566267902556863405 101451570212350463458823777)
      ·
        refine ⟨76088677659262847594117833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101451570212350463458823777 76088677659262847594117833)
        ·
          refine ⟨57066508244447135695588375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76088677659262847594117833 57066508244447135695588375)
          ·
            refine ⟨85599762366670703543382563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57066508244447135695588375 85599762366670703543382563)
            ·
              refine ⟨128399643550006055315073845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85599762366670703543382563 128399643550006055315073845)
              ·
                refine ⟨12037466582813067685788173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128399643550006055315073845 12037466582813067685788173)
                ·
                  refine ⟨4514049968554900382170565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12037466582813067685788173 4514049968554900382170565)
                  ·
                    refine ⟨846384369104043821656981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4514049968554900382170565 846384369104043821656981)
                    ·
                      rfl

theorem cell23_4944983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_4944983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944983 prefixEnd_4944983 := by exact prefixLift 4944983
  have htrace : WordTrace (prefixWord ++ tailWord_4944983) baseStart_4944983 baseEnd_4944983 := by
    simpa [prefixWord, tailWord_4944983, baseEnd_4944983] using wordTrace_append hprefix tailTrace_4944983
  have hstable : (prefixWord ++ tailWord_4944983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944983).length < 2 ^ (prefixWord ++ tailWord_4944983).sum := by decide
  have hdescent : baseEnd_4944983 < baseStart_4944983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944986 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6]
def baseStart_4944986 : Nat := 118140960795 + 4944986 * 2 ^ 59
def prefixEnd_4944986 : Nat := 4983230072969 + 3 ^ 40 * 4944986 * 2
def baseEnd_4944986 : Nat := 2539154647754094953233429

theorem tailTrace_4944986 : CollatzResearch.WordTrace tailWord_4944986 prefixEnd_4944986 2539154647754094953233429 := by
  unfold tailWord_4944986
  simp only [CollatzResearch.WordTrace]
  refine ⟨45089614115791933304233703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120238970975445155477956541 45089614115791933304233703)
  ·
    refine ⟨67634421173687899956350555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45089614115791933304233703 67634421173687899956350555)
    ·
      refine ⟨101451631760531849934525833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67634421173687899956350555 101451631760531849934525833)
      ·
        refine ⟨76088723820398887450894375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101451631760531849934525833 76088723820398887450894375)
        ·
          refine ⟨114133085730598331176341563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76088723820398887450894375 114133085730598331176341563)
          ·
            refine ⟨171199628595897496764512345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114133085730598331176341563 171199628595897496764512345)
            ·
              refine ⟨128399721446923122573384259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171199628595897496764512345 128399721446923122573384259)
              ·
                refine ⟨192599582170384683860076389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128399721446923122573384259 192599582170384683860076389)
                ·
                  refine ⟨36112421656947128223764323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 192599582170384683860076389 36112421656947128223764323)
                  ·
                    refine ⟨54168632485420692335646485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36112421656947128223764323 54168632485420692335646485)
                    ·
                      refine ⟨2539154647754094953233429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54168632485420692335646485 2539154647754094953233429)
                      ·
                        rfl

theorem cell23_4944986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_4944986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944986 prefixEnd_4944986 := by exact prefixLift 4944986
  have htrace : WordTrace (prefixWord ++ tailWord_4944986) baseStart_4944986 baseEnd_4944986 := by
    simpa [prefixWord, tailWord_4944986, baseEnd_4944986] using wordTrace_append hprefix tailTrace_4944986
  have hstable : (prefixWord ++ tailWord_4944986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944986).length < 2 ^ (prefixWord ++ tailWord_4944986).sum := by decide
  have hdescent : baseEnd_4944986 < baseStart_4944986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944993 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 4, 2, 3]
def baseStart_4944993 : Nat := 118140960795 + 4944993 * 2 ^ 59
def prefixEnd_4944993 : Nat := 4983230072969 + 3 ^ 40 * 4944993 * 2
def baseEnd_4944993 : Nat := 2539158242118676425845897

theorem tailTrace_4944993 : CollatzResearch.WordTrace tailWord_4944993 prefixEnd_4944993 2539158242118676425845897 := by
  unfold tailWord_4944993
  simp only [CollatzResearch.WordTrace]
  refine ⟨180358711774142373412439633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120239141182761582274959755 180358711774142373412439633)
  ·
    refine ⟨135269033830606780059329725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180358711774142373412439633 135269033830606780059329725)
    ·
      refine ⟨50725887686477542522248647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135269033830606780059329725 50725887686477542522248647)
      ·
        refine ⟨76088831529716313783372971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50725887686477542522248647 76088831529716313783372971)
        ·
          refine ⟨114133247294574470675059457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76088831529716313783372971 114133247294574470675059457)
          ·
            refine ⟨85599935470930853006294593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114133247294574470675059457 85599935470930853006294593)
            ·
              refine ⟨64199951603198139754720945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85599935470930853006294593 64199951603198139754720945)
              ·
                refine ⟨48149963702398604816040709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64199951603198139754720945 48149963702398604816040709)
                ·
                  refine ⟨9028118194199738403007633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48149963702398604816040709 9028118194199738403007633)
                  ·
                    refine ⟨6771088645649803802255725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9028118194199738403007633 6771088645649803802255725)
                    ·
                      refine ⟨2539158242118676425845897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6771088645649803802255725 2539158242118676425845897)
                      ·
                        rfl

theorem cell23_4944993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_4944993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944993 prefixEnd_4944993 := by exact prefixLift 4944993
  have htrace : WordTrace (prefixWord ++ tailWord_4944993) baseStart_4944993 baseEnd_4944993 := by
    simpa [prefixWord, tailWord_4944993, baseEnd_4944993] using wordTrace_append hprefix tailTrace_4944993
  have hstable : (prefixWord ++ tailWord_4944993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944993).length < 2 ^ (prefixWord ++ tailWord_4944993).sum := by decide
  have hdescent : baseEnd_4944993 < baseStart_4944993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4944996 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 10]
def baseStart_4944996 : Nat := 118140960795 + 4944996 * 2 ^ 59
def prefixEnd_4944996 : Nat := 4983230072969 + 3 ^ 40 * 4944996 * 2
def baseEnd_4944996 : Nat := 282128864728959990456487

theorem tailTrace_4944996 : CollatzResearch.WordTrace tailWord_4944996 prefixEnd_4944996 282128864728959990456487 := by
  unfold tailWord_4944996
  simp only [CollatzResearch.WordTrace]
  refine ⟨90179410596565752462399421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120239214128754336616532561 90179410596565752462399421)
  ·
    refine ⟨33817278973712157173399783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90179410596565752462399421 33817278973712157173399783)
    ·
      refine ⟨50725918460568235760099675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33817278973712157173399783 50725918460568235760099675)
      ·
        refine ⟨76088877690852353640149513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50725918460568235760099675 76088877690852353640149513)
        ·
          refine ⟨57066658268139265230112135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76088877690852353640149513 57066658268139265230112135)
          ·
            refine ⟨85599987402208897845168203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57066658268139265230112135 85599987402208897845168203)
            ·
              refine ⟨128399981103313346767752305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85599987402208897845168203 128399981103313346767752305)
              ·
                refine ⟨96299985827485010075814229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128399981103313346767752305 96299985827485010075814229)
                ·
                  refine ⟨282128864728959990456487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 96299985827485010075814229 282128864728959990456487)
                  ·
                    rfl

theorem cell23_4944996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_4944996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4944996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4944996 prefixEnd_4944996 := by exact prefixLift 4944996
  have htrace : WordTrace (prefixWord ++ tailWord_4944996) baseStart_4944996 baseEnd_4944996 := by
    simpa [prefixWord, tailWord_4944996, baseEnd_4944996] using wordTrace_append hprefix tailTrace_4944996
  have hstable : (prefixWord ++ tailWord_4944996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4944996).length < 2 ^ (prefixWord ++ tailWord_4944996).sum := by decide
  have hdescent : baseEnd_4944996 < baseStart_4944996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4944996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945060 : List Nat := [2, 3, 1, 2, 3, 1, 1, 4, 1, 5]
def baseStart_4945060 : Nat := 118140960795 + 4945060 * 2 ^ 59
def prefixEnd_4945060 : Nat := 4983230072969 + 3 ^ 40 * 4945060 * 2
def baseEnd_4945060 : Nat := 846397548440842554569363

theorem tailTrace_4945060 : CollatzResearch.WordTrace tailWord_4945060 prefixEnd_4945060 846397548440842554569363 := by
  unfold tailWord_4945060
  simp only [CollatzResearch.WordTrace]
  refine ⟨90180577732449821927564317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120240770309933095903419089 90180577732449821927564317)
  ·
    refine ⟨33817716649668683222836619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90180577732449821927564317 33817716649668683222836619)
    ·
      refine ⟨50726574974503024834254929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33817716649668683222836619 50726574974503024834254929)
      ·
        refine ⟨38044931230877268625691197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50726574974503024834254929 38044931230877268625691197)
        ·
          refine ⟨14266849211578975734634199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38044931230877268625691197 14266849211578975734634199)
          ·
            refine ⟨21400273817368463601951299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14266849211578975734634199 21400273817368463601951299)
            ·
              refine ⟨32100410726052695402926949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21400273817368463601951299 32100410726052695402926949)
              ·
                refine ⟨6018827011134880388048803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32100410726052695402926949 6018827011134880388048803)
                ·
                  refine ⟨9028240516702320582073205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6018827011134880388048803 9028240516702320582073205)
                  ·
                    refine ⟨846397548440842554569363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9028240516702320582073205 846397548440842554569363)
                    ·
                      rfl

theorem cell23_4945060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_4945060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945060 prefixEnd_4945060 := by exact prefixLift 4945060
  have htrace : WordTrace (prefixWord ++ tailWord_4945060) baseStart_4945060 baseEnd_4945060 := by
    simpa [prefixWord, tailWord_4945060, baseEnd_4945060] using wordTrace_append hprefix tailTrace_4945060
  have hstable : (prefixWord ++ tailWord_4945060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945060).length < 2 ^ (prefixWord ++ tailWord_4945060).sum := by decide
  have hdescent : baseEnd_4945060 < baseStart_4945060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945074 : List Nat := [3, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3]
def baseStart_4945074 : Nat := 118140960795 + 4945074 * 2 ^ 59
def prefixEnd_4945074 : Nat := 4983230072969 + 3 ^ 40 * 4945074 * 2
def baseEnd_4945074 : Nat := 2539199834051690608933025

theorem tailTrace_4945074 : CollatzResearch.WordTrace tailWord_4945074 prefixEnd_4945074 2539199834051690608933025 := by
  unfold tailWord_4945074
  simp only [CollatzResearch.WordTrace]
  refine ⟨45090416521712231061534569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120241110724565949497425517 45090416521712231061534569)
  ·
    refine ⟨33817812391284173296150927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45090416521712231061534569 33817812391284173296150927)
    ·
      refine ⟨50726718586926259944226391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33817812391284173296150927 50726718586926259944226391)
      ·
        refine ⟨76090077880389389916339587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50726718586926259944226391 76090077880389389916339587)
        ·
          refine ⟨114135116820584084874509381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76090077880389389916339587 114135116820584084874509381)
          ·
            refine ⟨21400334403859515913970509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114135116820584084874509381 21400334403859515913970509)
            ·
              refine ⟨8025125401447318467738941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21400334403859515913970509 8025125401447318467738941)
              ·
                refine ⟨3009422025542744425402103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8025125401447318467738941 3009422025542744425402103)
                ·
                  refine ⟨4514133038314116638103155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3009422025542744425402103 4514133038314116638103155)
                  ·
                    refine ⟨6771199557471174957154733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4514133038314116638103155 6771199557471174957154733)
                    ·
                      refine ⟨2539199834051690608933025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6771199557471174957154733 2539199834051690608933025)
                      ·
                        rfl

theorem cell23_4945074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3].length) (baseStart_4945074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945074 prefixEnd_4945074 := by exact prefixLift 4945074
  have htrace : WordTrace (prefixWord ++ tailWord_4945074) baseStart_4945074 baseEnd_4945074 := by
    simpa [prefixWord, tailWord_4945074, baseEnd_4945074] using wordTrace_append hprefix tailTrace_4945074
  have hstable : (prefixWord ++ tailWord_4945074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945074).length < 2 ^ (prefixWord ++ tailWord_4945074).sum := by decide
  have hdescent : baseEnd_4945074 < baseStart_4945074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945127 : List Nat := [1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_4945127 : Nat := 118140960795 + 4945127 * 2 ^ 59
def prefixEnd_4945127 : Nat := 4983230072969 + 3 ^ 40 * 4945127 * 2
def baseEnd_4945127 : Nat := 2539227048526378901570281

theorem tailTrace_4945127 : CollatzResearch.WordTrace tailWord_4945127 prefixEnd_4945127 2539227048526378901570281 := by
  unfold tailWord_4945127
  simp only [CollatzResearch.WordTrace]
  refine ⟨180363599155656914297817635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120242399437104609531878423 180363599155656914297817635)
  ·
    refine ⟨270545398733485371446726453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180363599155656914297817635 270545398733485371446726453)
    ·
      refine ⟨25363631131264253573130605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 270545398733485371446726453 25363631131264253573130605)
      ·
        refine ⟨9511361674224095089923977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25363631131264253573130605 9511361674224095089923977)
        ·
          refine ⟨7133521255668071317442983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9511361674224095089923977 7133521255668071317442983)
          ·
            refine ⟨10700281883502106976164475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7133521255668071317442983 10700281883502106976164475)
            ·
              refine ⟨16050422825253160464246713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10700281883502106976164475 16050422825253160464246713)
              ·
                refine ⟨12037817118939870348185035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16050422825253160464246713 12037817118939870348185035)
                ·
                  refine ⟨18056725678409805522277553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12037817118939870348185035 18056725678409805522277553)
                  ·
                    refine ⟨13542544258807354141708165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18056725678409805522277553 13542544258807354141708165)
                    ·
                      refine ⟨2539227048526378901570281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13542544258807354141708165 2539227048526378901570281)
                      ·
                        rfl

theorem cell23_4945127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_4945127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945127 prefixEnd_4945127 := by exact prefixLift 4945127
  have htrace : WordTrace (prefixWord ++ tailWord_4945127) baseStart_4945127 baseEnd_4945127 := by
    simpa [prefixWord, tailWord_4945127, baseEnd_4945127] using wordTrace_append hprefix tailTrace_4945127
  have hstable : (prefixWord ++ tailWord_4945127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945127).length < 2 ^ (prefixWord ++ tailWord_4945127).sum := by decide
  have hdescent : baseEnd_4945127 < baseStart_4945127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945130 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_4945130 : Nat := 118140960795 + 4945130 * 2 ^ 59
def prefixEnd_4945130 : Nat := 4983230072969 + 3 ^ 40 * 4945130 * 2
def baseEnd_4945130 : Nat := 2539228588968342389832767

theorem tailTrace_4945130 : CollatzResearch.WordTrace tailWord_4945130 prefixEnd_4945130 2539228588968342389832767 := by
  unfold tailWord_4945130
  simp only [CollatzResearch.WordTrace]
  refine ⟨45090927143661511452544211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120242472383097363873451229 45090927143661511452544211)
  ·
    refine ⟨67636390715492267178816317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45090927143661511452544211 67636390715492267178816317)
    ·
      refine ⟨25363646518309600192056119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67636390715492267178816317 25363646518309600192056119)
      ·
        refine ⟨38045469777464400288084179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25363646518309600192056119 38045469777464400288084179)
        ·
          refine ⟨57068204666196600432126269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38045469777464400288084179 57068204666196600432126269)
          ·
            refine ⟨21400576749823725162047351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57068204666196600432126269 21400576749823725162047351)
            ·
              refine ⟨32100865124735587743071027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21400576749823725162047351 32100865124735587743071027)
              ·
                refine ⟨48151297687103381614606541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32100865124735587743071027 48151297687103381614606541)
                ·
                  refine ⟨18056736632663768105477453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48151297687103381614606541 18056736632663768105477453)
                  ·
                    refine ⟨6771276237248913039554045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18056736632663768105477453 6771276237248913039554045)
                    ·
                      refine ⟨2539228588968342389832767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6771276237248913039554045 2539228588968342389832767)
                      ·
                        rfl

theorem cell23_4945130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_4945130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945130 prefixEnd_4945130 := by exact prefixLift 4945130
  have htrace : WordTrace (prefixWord ++ tailWord_4945130) baseStart_4945130 baseEnd_4945130 := by
    simpa [prefixWord, tailWord_4945130, baseEnd_4945130] using wordTrace_append hprefix tailTrace_4945130
  have hstable : (prefixWord ++ tailWord_4945130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945130).length < 2 ^ (prefixWord ++ tailWord_4945130).sum := by decide
  have hdescent : baseEnd_4945130 < baseStart_4945130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945150 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_4945150 : Nat := 118140960795 + 4945150 * 2 ^ 59
def prefixEnd_4945150 : Nat := 4983230072969 + 3 ^ 40 * 4945150 * 2
def baseEnd_4945150 : Nat := 846412952860477437194225

theorem tailTrace_4945150 : CollatzResearch.WordTrace tailWord_4945150 prefixEnd_4945150 846412952860477437194225 := by
  unfold tailWord_4945150
  simp only [CollatzResearch.WordTrace]
  refine ⟨22545554754321698653238113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120242958689715726150603269 22545554754321698653238113)
  ·
    refine ⟨16909166065741273989928585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22545554754321698653238113 16909166065741273989928585)
    ·
      refine ⟨12681874549305955492446439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16909166065741273989928585 12681874549305955492446439)
      ·
        refine ⟨19022811823958933238669659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12681874549305955492446439 19022811823958933238669659)
        ·
          refine ⟨28534217735938399858004489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19022811823958933238669659 28534217735938399858004489)
          ·
            refine ⟨21400663301953799893503367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28534217735938399858004489 21400663301953799893503367)
            ·
              refine ⟨32100994952930699840255051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21400663301953799893503367 32100994952930699840255051)
              ·
                refine ⟨48151492429396049760382577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32100994952930699840255051 48151492429396049760382577)
                ·
                  refine ⟨36113619322047037320286933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48151492429396049760382577 36113619322047037320286933)
                  ·
                    refine ⟨846412952860477437194225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36113619322047037320286933 846412952860477437194225)
                    ·
                      rfl

theorem cell23_4945150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_4945150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945150 prefixEnd_4945150 := by exact prefixLift 4945150
  have htrace : WordTrace (prefixWord ++ tailWord_4945150) baseStart_4945150 baseEnd_4945150 := by
    simpa [prefixWord, tailWord_4945150, baseEnd_4945150] using wordTrace_append hprefix tailTrace_4945150
  have hstable : (prefixWord ++ tailWord_4945150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945150).length < 2 ^ (prefixWord ++ tailWord_4945150).sum := by decide
  have hdescent : baseEnd_4945150 < baseStart_4945150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945154 : List Nat := [3, 4, 1, 1, 4, 1, 1, 8]
def baseStart_4945154 : Nat := 118140960795 + 4945154 * 2 ^ 59
def prefixEnd_4945154 : Nat := 4983230072969 + 3 ^ 40 * 4945154 * 2
def baseEnd_4945154 : Nat := 94045959722372233182691

theorem tailTrace_4945154 : CollatzResearch.WordTrace tailWord_4945154 prefixEnd_4945154 94045959722372233182691 := by
  unfold tailWord_4945154
  simp only [CollatzResearch.WordTrace]
  refine ⟨45091145981639774477262629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120243055951039398606033677 45091145981639774477262629)
  ·
    refine ⟨8454589871557457714486743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45091145981639774477262629 8454589871557457714486743)
    ·
      refine ⟨12681884807336186571730115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8454589871557457714486743 12681884807336186571730115)
      ·
        refine ⟨19022827211004279857595173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12681884807336186571730115 19022827211004279857595173)
        ·
          refine ⟨3566780102063302473299095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19022827211004279857595173 3566780102063302473299095)
          ·
            refine ⟨5350170153094953709948643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3566780102063302473299095 5350170153094953709948643)
            ·
              refine ⟨8025255229642430564922965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5350170153094953709948643 8025255229642430564922965)
              ·
                refine ⟨94045959722372233182691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8025255229642430564922965 94045959722372233182691)
                ·
                  rfl

theorem cell23_4945154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 8].length) (baseStart_4945154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945154 prefixEnd_4945154 := by exact prefixLift 4945154
  have htrace : WordTrace (prefixWord ++ tailWord_4945154) baseStart_4945154 baseEnd_4945154 := by
    simpa [prefixWord, tailWord_4945154, baseEnd_4945154] using wordTrace_append hprefix tailTrace_4945154
  have hstable : (prefixWord ++ tailWord_4945154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945154).length < 2 ^ (prefixWord ++ tailWord_4945154).sum := by decide
  have hdescent : baseEnd_4945154 < baseStart_4945154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945163 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 1, 8]
def baseStart_4945163 : Nat := 118140960795 + 4945163 * 2 ^ 59
def prefixEnd_4945163 : Nat := 4983230072969 + 3 ^ 40 * 4945163 * 2
def baseEnd_4945163 : Nat := 846415177943313586906705

theorem tailTrace_4945163 : CollatzResearch.WordTrace tailWord_4945163 prefixEnd_4945163 846415177943313586906705 := by
  unfold tailWord_4945163
  simp only [CollatzResearch.WordTrace]
  refine ⟨180364912183526492446128143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120243274789017661630752095 180364912183526492446128143)
  ·
    refine ⟨270547368275289738669192215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180364912183526492446128143 270547368275289738669192215)
    ·
      refine ⟨405821052412934608003788323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270547368275289738669192215 405821052412934608003788323)
      ·
        refine ⟨608731578619401912005682485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405821052412934608003788323 608731578619401912005682485)
        ·
          refine ⟨57068585495568929250532733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 608731578619401912005682485 57068585495568929250532733)
          ·
            refine ⟨21400719560838348468949775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57068585495568929250532733 21400719560838348468949775)
            ·
              refine ⟨32101079341257522703424663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21400719560838348468949775 32101079341257522703424663)
              ·
                refine ⟨48151619011886284055136995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32101079341257522703424663 48151619011886284055136995)
                ·
                  refine ⟨72227428517829426082705493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48151619011886284055136995 72227428517829426082705493)
                  ·
                    refine ⟨846415177943313586906705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72227428517829426082705493 846415177943313586906705)
                    ·
                      rfl

theorem cell23_4945163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 8].length) (baseStart_4945163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945163 prefixEnd_4945163 := by exact prefixLift 4945163
  have htrace : WordTrace (prefixWord ++ tailWord_4945163) baseStart_4945163 baseEnd_4945163 := by
    simpa [prefixWord, tailWord_4945163, baseEnd_4945163] using wordTrace_append hprefix tailTrace_4945163
  have hstable : (prefixWord ++ tailWord_4945163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945163).length < 2 ^ (prefixWord ++ tailWord_4945163).sum := by decide
  have hdescent : baseEnd_4945163 < baseStart_4945163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945187 : List Nat := [1, 1, 1, 4, 2, 3, 2, 2, 1, 4, 2]
def baseStart_4945187 : Nat := 118140960795 + 4945187 * 2 ^ 59
def prefixEnd_4945187 : Nat := 4983230072969 + 3 ^ 40 * 4945187 * 2
def baseEnd_4945187 : Nat := 2539257857365648666820005

theorem tailTrace_4945187 : CollatzResearch.WordTrace tailWord_4945187 prefixEnd_4945187 2539257857365648666820005 := by
  unfold tailWord_4945187
  simp only [CollatzResearch.WordTrace]
  refine ⟨180365787535439544545001815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120243858356959696363334543 180365787535439544545001815)
  ·
    refine ⟨270548681303159316817502723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180365787535439544545001815 270548681303159316817502723)
    ·
      refine ⟨405823021954738975226254085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270548681303159316817502723 405823021954738975226254085)
      ·
        refine ⟨76091816616513557854922641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 405823021954738975226254085 76091816616513557854922641)
        ·
          refine ⟨57068862462385168391191981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76091816616513557854922641 57068862462385168391191981)
          ·
            refine ⟨21400823423394438146696993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57068862462385168391191981 21400823423394438146696993)
            ·
              refine ⟨16050617567545828610022745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21400823423394438146696993 16050617567545828610022745)
              ·
                refine ⟨12037963175659371457517059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16050617567545828610022745 12037963175659371457517059)
                ·
                  refine ⟨18056944763489057186275589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12037963175659371457517059 18056944763489057186275589)
                  ·
                    refine ⟨3385677143154198222426673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18056944763489057186275589 3385677143154198222426673)
                    ·
                      refine ⟨2539257857365648666820005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3385677143154198222426673 2539257857365648666820005)
                      ·
                        rfl

theorem cell23_4945187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_4945187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945187 prefixEnd_4945187 := by exact prefixLift 4945187
  have htrace : WordTrace (prefixWord ++ tailWord_4945187) baseStart_4945187 baseEnd_4945187 := by
    simpa [prefixWord, tailWord_4945187, baseEnd_4945187] using wordTrace_append hprefix tailTrace_4945187
  have hstable : (prefixWord ++ tailWord_4945187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945187).length < 2 ^ (prefixWord ++ tailWord_4945187).sum := by decide
  have hdescent : baseEnd_4945187 < baseStart_4945187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945197 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_4945197 : Nat := 118140960795 + 4945197 * 2 ^ 59
def prefixEnd_4945197 : Nat := 4983230072969 + 3 ^ 40 * 4945197 * 2
def baseEnd_4945197 : Nat := 846420997390731209231653

theorem tailTrace_4945197 : CollatzResearch.WordTrace tailWord_4945197 prefixEnd_4945197 846420997390731209231653 := by
  unfold tailWord_4945197
  simp only [CollatzResearch.WordTrace]
  refine ⟨180366152265403316252865845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120244101510268877501910563 180366152265403316252865845)
  ·
    refine ⟨16909326774881560898706173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 180366152265403316252865845 16909326774881560898706173)
    ·
      refine ⟨6340997540580585337014815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16909326774881560898706173 6340997540580585337014815)
      ·
        refine ⟨9511496310870878005522223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6340997540580585337014815 9511496310870878005522223)
        ·
          refine ⟨14267244466306317008283335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9511496310870878005522223 14267244466306317008283335)
          ·
            refine ⟨21400866699459475512425003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14267244466306317008283335 21400866699459475512425003)
            ·
              refine ⟨32101300049189213268637505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21400866699459475512425003 32101300049189213268637505)
              ·
                refine ⟨24075975036891909951478129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32101300049189213268637505 24075975036891909951478129)
                ·
                  refine ⟨18056981277668932463608597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24075975036891909951478129 18056981277668932463608597)
                  ·
                    refine ⟨846420997390731209231653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18056981277668932463608597 846420997390731209231653)
                    ·
                      rfl

theorem cell23_4945197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_4945197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945197 prefixEnd_4945197 := by exact prefixLift 4945197
  have htrace : WordTrace (prefixWord ++ tailWord_4945197) baseStart_4945197 baseEnd_4945197 := by
    simpa [prefixWord, tailWord_4945197, baseEnd_4945197] using wordTrace_append hprefix tailTrace_4945197
  have hstable : (prefixWord ++ tailWord_4945197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945197).length < 2 ^ (prefixWord ++ tailWord_4945197).sum := by decide
  have hdescent : baseEnd_4945197 < baseStart_4945197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945210 : List Nat := [3, 1, 1, 1, 4, 1, 4, 1, 7]
def baseStart_4945210 : Nat := 118140960795 + 4945210 * 2 ^ 59
def prefixEnd_4945210 : Nat := 4983230072969 + 3 ^ 40 * 4945210 * 2
def baseEnd_4945210 : Nat := 282141074157855786314711

theorem tailTrace_4945210 : CollatzResearch.WordTrace tailWord_4945210 prefixEnd_4945210 282141074157855786314711 := by
  unfold tailWord_4945210
  simp only [CollatzResearch.WordTrace]
  refine ⟨45091656603589054868272271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120244417609570812982059389 45091656603589054868272271)
  ·
    refine ⟨67637484905383582302408407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45091656603589054868272271 67637484905383582302408407)
    ·
      refine ⟨101456227358075373453612611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67637484905383582302408407 101456227358075373453612611)
      ·
        refine ⟨152184341037113060180418917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101456227358075373453612611 152184341037113060180418917)
        ·
          refine ⟨28534563944458698783828547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152184341037113060180418917 28534563944458698783828547)
          ·
            refine ⟨42801845916688048175742821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28534563944458698783828547 42801845916688048175742821)
            ·
              refine ⟨8025346109379009032951779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42801845916688048175742821 8025346109379009032951779)
              ·
                refine ⟨12038019164068513549427669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8025346109379009032951779 12038019164068513549427669)
                ·
                  refine ⟨282141074157855786314711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12038019164068513549427669 282141074157855786314711)
                  ·
                    rfl

theorem cell23_4945210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 7].length) (baseStart_4945210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945210 prefixEnd_4945210 := by exact prefixLift 4945210
  have htrace : WordTrace (prefixWord ++ tailWord_4945210) baseStart_4945210 baseEnd_4945210 := by
    simpa [prefixWord, tailWord_4945210, baseEnd_4945210] using wordTrace_append hprefix tailTrace_4945210
  have hstable : (prefixWord ++ tailWord_4945210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945210).length < 2 ^ (prefixWord ++ tailWord_4945210).sum := by decide
  have hdescent : baseEnd_4945210 < baseStart_4945210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945217 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_4945217 : Nat := 118140960795 + 4945217 * 2 ^ 59
def prefixEnd_4945217 : Nat := 4983230072969 + 3 ^ 40 * 4945217 * 2
def baseEnd_4945217 : Nat := 2539273261785283549444867

theorem tailTrace_4945217 : CollatzResearch.WordTrace tailWord_4945217 prefixEnd_4945217 2539273261785283549444867 := by
  unfold tailWord_4945217
  simp only [CollatzResearch.WordTrace]
  refine ⟨180366881725330859668593905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120244587816887239779062603 180366881725330859668593905)
  ·
    refine ⟨135275161293998144751445429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180366881725330859668593905 135275161293998144751445429)
    ·
      refine ⟨12682046371312326070448009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135275161293998144751445429 12682046371312326070448009)
      ·
        refine ⟨9511534778484244552836007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12682046371312326070448009 9511534778484244552836007)
        ·
          refine ⟨14267302167726366829254011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9511534778484244552836007 14267302167726366829254011)
          ·
            refine ⟨21400953251589550243881017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14267302167726366829254011 21400953251589550243881017)
            ·
              refine ⟨16050714938692162682910763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21400953251589550243881017 16050714938692162682910763)
              ·
                refine ⟨24076072408038244024366145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16050714938692162682910763 24076072408038244024366145)
                ·
                  refine ⟨18057054306028683018274609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24076072408038244024366145 18057054306028683018274609)
                  ·
                    refine ⟨13542790729521512263705957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18057054306028683018274609 13542790729521512263705957)
                    ·
                      refine ⟨2539273261785283549444867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13542790729521512263705957 2539273261785283549444867)
                      ·
                        rfl

theorem cell23_4945217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_4945217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945217 prefixEnd_4945217 := by exact prefixLift 4945217
  have htrace : WordTrace (prefixWord ++ tailWord_4945217) baseStart_4945217 baseEnd_4945217 := by
    simpa [prefixWord, tailWord_4945217, baseEnd_4945217] using wordTrace_append hprefix tailTrace_4945217
  have hstable : (prefixWord ++ tailWord_4945217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945217).length < 2 ^ (prefixWord ++ tailWord_4945217).sum := by decide
  have hdescent : baseEnd_4945217 < baseStart_4945217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945240 : List Nat := [2, 1, 2, 2, 1, 1, 4, 3, 2, 5]
def baseStart_4945240 : Nat := 118140960795 + 4945240 * 2 ^ 59
def prefixEnd_4945240 : Nat := 4983230072969 + 3 ^ 40 * 4945240 * 2
def baseEnd_4945240 : Nat := 846428357280112319819087

theorem tailTrace_4945240 : CollatzResearch.WordTrace tailWord_4945240 prefixEnd_4945240 846428357280112319819087 := by
  unfold tailWord_4945240
  simp only [CollatzResearch.WordTrace]
  refine ⟨90183860302123767298340587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120245147069498356397787449 90183860302123767298340587)
  ·
    refine ⟨135275790453185650947510881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90183860302123767298340587 135275790453185650947510881)
    ·
      refine ⟨101456842839889238210633161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135275790453185650947510881 101456842839889238210633161)
      ·
        refine ⟨76092632129916928657974871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101456842839889238210633161 76092632129916928657974871)
        ·
          refine ⟨114138948194875392986962307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76092632129916928657974871 114138948194875392986962307)
          ·
            refine ⟨171208422292313089480443461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114138948194875392986962307 171208422292313089480443461)
            ·
              refine ⟨32101579179808704277583149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171208422292313089480443461 32101579179808704277583149)
              ·
                refine ⟨12038092192428264104093681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32101579179808704277583149 12038092192428264104093681)
                ·
                  refine ⟨9028569144321198078070261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12038092192428264104093681 9028569144321198078070261)
                  ·
                    refine ⟨846428357280112319819087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9028569144321198078070261 846428357280112319819087)
                    ·
                      rfl

theorem cell23_4945240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_4945240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945240 prefixEnd_4945240 := by exact prefixLift 4945240
  have htrace : WordTrace (prefixWord ++ tailWord_4945240) baseStart_4945240 baseEnd_4945240 := by
    simpa [prefixWord, tailWord_4945240, baseEnd_4945240] using wordTrace_append hprefix tailTrace_4945240
  have hstable : (prefixWord ++ tailWord_4945240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945240).length < 2 ^ (prefixWord ++ tailWord_4945240).sum := by decide
  have hdescent : baseEnd_4945240 < baseStart_4945240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945277 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 1, 6, 2]
def baseStart_4945277 : Nat := 118140960795 + 4945277 * 2 ^ 59
def prefixEnd_4945277 : Nat := 4983230072969 + 3 ^ 40 * 4945277 * 2
def baseEnd_4945277 : Nat := 2539304070624553314694591

theorem tailTrace_4945277 : CollatzResearch.WordTrace tailWord_4945277 prefixEnd_4945277 2539304070624553314694591 := by
  unfold tailWord_4945277
  simp only [CollatzResearch.WordTrace]
  refine ⟨180369070105113489915778085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120246046736742326610518723 180369070105113489915778085)
  ·
    refine ⟨33819200644708779359208391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180369070105113489915778085 33819200644708779359208391)
    ·
      refine ⟨50728800967063169038812587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33819200644708779359208391 50728800967063169038812587)
      ·
        refine ⟨76093201450594753558218881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50728800967063169038812587 76093201450594753558218881)
        ·
          refine ⟨57069901087946065168664161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76093201450594753558218881 57069901087946065168664161)
          ·
            refine ⟨42802425815959548876498121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57069901087946065168664161 42802425815959548876498121)
            ·
              refine ⟨32101819361969661657373591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42802425815959548876498121 32101819361969661657373591)
              ·
                refine ⟨48152729042954492486060387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32101819361969661657373591 48152729042954492486060387)
                ·
                  refine ⟨72229093564431738729090581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48152729042954492486060387 72229093564431738729090581)
                  ·
                    refine ⟨3385738760832737752926121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72229093564431738729090581 3385738760832737752926121)
                    ·
                      refine ⟨2539304070624553314694591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3385738760832737752926121 2539304070624553314694591)
                      ·
                        rfl

theorem cell23_4945277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_4945277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945277 prefixEnd_4945277 := by exact prefixLift 4945277
  have htrace : WordTrace (prefixWord ++ tailWord_4945277) baseStart_4945277 baseEnd_4945277 := by
    simpa [prefixWord, tailWord_4945277, baseEnd_4945277] using wordTrace_append hprefix tailTrace_4945277
  have hstable : (prefixWord ++ tailWord_4945277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945277).length < 2 ^ (prefixWord ++ tailWord_4945277).sum := by decide
  have hdescent : baseEnd_4945277 < baseStart_4945277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945280 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 3]
def baseStart_4945280 : Nat := 118140960795 + 4945280 * 2 ^ 59
def prefixEnd_4945280 : Nat := 4983230072969 + 3 ^ 40 * 4945280 * 2
def baseEnd_4945280 : Nat := 2539305611066516802957077

theorem tailTrace_4945280 : CollatzResearch.WordTrace tailWord_4945280 prefixEnd_4945280 2539305611066516802957077 := by
  unfold tailWord_4945280
  simp only [CollatzResearch.WordTrace]
  refine ⟨90184589762051310714068647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120246119682735080952091529 90184589762051310714068647)
  ·
    refine ⟨135276884643076966071102971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90184589762051310714068647 135276884643076966071102971)
    ·
      refine ⟨202915326964615449106654457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135276884643076966071102971 202915326964615449106654457)
      ·
        refine ⟨152186495223461586829990843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202915326964615449106654457 152186495223461586829990843)
        ·
          refine ⟨228279742835192380244986265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152186495223461586829990843 228279742835192380244986265)
          ·
            refine ⟨171209807126394285183739699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228279742835192380244986265 171209807126394285183739699)
            ·
              refine ⟨256814710689591427775609549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171209807126394285183739699 256814710689591427775609549)
              ·
                refine ⟨96305516508596785415853581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 256814710689591427775609549 96305516508596785415853581)
                ·
                  refine ⟨36114568690723794530945093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96305516508596785415853581 36114568690723794530945093)
                  ·
                    refine ⟨6771481629510711474552205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36114568690723794530945093 6771481629510711474552205)
                    ·
                      refine ⟨2539305611066516802957077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6771481629510711474552205 2539305611066516802957077)
                      ·
                        rfl

theorem cell23_4945280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_4945280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945280 prefixEnd_4945280 := by exact prefixLift 4945280
  have htrace : WordTrace (prefixWord ++ tailWord_4945280) baseStart_4945280 baseEnd_4945280 := by
    simpa [prefixWord, tailWord_4945280, baseEnd_4945280] using wordTrace_append hprefix tailTrace_4945280
  have hstable : (prefixWord ++ tailWord_4945280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945280).length < 2 ^ (prefixWord ++ tailWord_4945280).sum := by decide
  have hdescent : baseEnd_4945280 < baseStart_4945280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945314 : List Nat := [3, 3, 1, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_4945314 : Nat := 118140960795 + 4945314 * 2 ^ 59
def prefixEnd_4945314 : Nat := 4983230072969 + 3 ^ 40 * 4945314 * 2
def baseEnd_4945314 : Nat := 2539323069408769669931921

theorem tailTrace_4945314 : CollatzResearch.WordTrace tailWord_4945314 prefixEnd_4945314 2539323069408769669931921 := by
  unfold tailWord_4945314
  simp only [CollatzResearch.WordTrace]
  refine ⟨45092604901494861308718749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120246946403986296823249997 45092604901494861308718749)
  ·
    refine ⟨16909726838060572990769531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45092604901494861308718749 16909726838060572990769531)
    ·
      refine ⟨25364590257090859486154297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16909726838060572990769531 25364590257090859486154297)
      ·
        refine ⟨19023442692818144614615723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25364590257090859486154297 19023442692818144614615723)
        ·
          refine ⟨28535164039227216921923585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19023442692818144614615723 28535164039227216921923585)
          ·
            refine ⟨21401373029420412691442689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28535164039227216921923585 21401373029420412691442689)
            ·
              refine ⟨16051029772065309518582017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21401373029420412691442689 16051029772065309518582017)
              ·
                refine ⟨12038272329048982138936513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16051029772065309518582017 12038272329048982138936513)
                ·
                  refine ⟨9028704246786736604202385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12038272329048982138936513 9028704246786736604202385)
                  ·
                    refine ⟨6771528185090052453151789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9028704246786736604202385 6771528185090052453151789)
                    ·
                      refine ⟨2539323069408769669931921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6771528185090052453151789 2539323069408769669931921)
                      ·
                        rfl

theorem cell23_4945314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_4945314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945314 prefixEnd_4945314 := by exact prefixLift 4945314
  have htrace : WordTrace (prefixWord ++ tailWord_4945314) baseStart_4945314 baseEnd_4945314 := by
    simpa [prefixWord, tailWord_4945314, baseEnd_4945314] using wordTrace_append hprefix tailTrace_4945314
  have hstable : (prefixWord ++ tailWord_4945314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945314).length < 2 ^ (prefixWord ++ tailWord_4945314).sum := by decide
  have hdescent : baseEnd_4945314 < baseStart_4945314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945327 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 7, 1, 3]
def baseStart_4945327 : Nat := 118140960795 + 4945327 * 2 ^ 59
def prefixEnd_4945327 : Nat := 4983230072969 + 3 ^ 40 * 4945327 * 2
def baseEnd_4945327 : Nat := 2539329744657278119069361

theorem tailTrace_4945327 : CollatzResearch.WordTrace tailWord_4945327 prefixEnd_4945327 2539329744657278119069361 := by
  unfold tailWord_4945327
  simp only [CollatzResearch.WordTrace]
  refine ⟨180370893754932348455098235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120247262503288232303398823 180370893754932348455098235)
  ·
    refine ⟨270556340632398522682647353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180370893754932348455098235 270556340632398522682647353)
    ·
      refine ⟨202917255474298892011985515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270556340632398522682647353 202917255474298892011985515)
      ·
        refine ⟨304375883211448338017978273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202917255474298892011985515 304375883211448338017978273)
        ·
          refine ⟨228281912408586253513483705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304375883211448338017978273 228281912408586253513483705)
          ·
            refine ⟨171211434306439690135112779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228281912408586253513483705 171211434306439690135112779)
            ·
              refine ⟨256817151459659535202669169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171211434306439690135112779 256817151459659535202669169)
              ·
                refine ⟨192612863594744651402001877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256817151459659535202669169 192612863594744651402001877)
                ·
                  refine ⟨4514363990501827767234419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 192612863594744651402001877 4514363990501827767234419)
                  ·
                    refine ⟨6771545985752741650851629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4514363990501827767234419 6771545985752741650851629)
                    ·
                      refine ⟨2539329744657278119069361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6771545985752741650851629 2539329744657278119069361)
                      ·
                        rfl

theorem cell23_4945327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 1, 3].length) (baseStart_4945327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945327 prefixEnd_4945327 := by exact prefixLift 4945327
  have htrace : WordTrace (prefixWord ++ tailWord_4945327) baseStart_4945327 baseEnd_4945327 := by
    simpa [prefixWord, tailWord_4945327, baseEnd_4945327] using wordTrace_append hprefix tailTrace_4945327
  have hstable : (prefixWord ++ tailWord_4945327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945327).length < 2 ^ (prefixWord ++ tailWord_4945327).sum := by decide
  have hdescent : baseEnd_4945327 < baseStart_4945327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945354 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 1, 5, 2]
def baseStart_4945354 : Nat := 118140960795 + 4945354 * 2 ^ 59
def prefixEnd_4945354 : Nat := 4983230072969 + 3 ^ 40 * 4945354 * 2
def baseEnd_4945354 : Nat := 2539343608634949513431737

theorem tailTrace_4945354 : CollatzResearch.WordTrace tailWord_4945354 prefixEnd_4945354 2539343608634949513431737 := by
  unfold tailWord_4945354
  simp only [CollatzResearch.WordTrace]
  refine ⟨45092969631458633016582779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120247919017223021377554077 45092969631458633016582779)
  ·
    refine ⟨67639454447187949524874169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45092969631458633016582779 67639454447187949524874169)
    ·
      refine ⟨50729590835390962143655627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67639454447187949524874169 50729590835390962143655627)
      ·
        refine ⟨76094386253086443215483441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50729590835390962143655627 76094386253086443215483441)
        ·
          refine ⟨57070789689814832411612581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76094386253086443215483441 57070789689814832411612581)
          ·
            refine ⟨10700773066840281077177359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57070789689814832411612581 10700773066840281077177359)
            ·
              refine ⟨16051159600260421615766039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10700773066840281077177359 16051159600260421615766039)
              ·
                refine ⟨24076739400390632423649059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16051159600260421615766039 24076739400390632423649059)
                ·
                  refine ⟨36115109100585948635473589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24076739400390632423649059 36115109100585948635473589)
                  ·
                    refine ⟨3385791478179932684575649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36115109100585948635473589 3385791478179932684575649)
                    ·
                      refine ⟨2539343608634949513431737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3385791478179932684575649 2539343608634949513431737)
                      ·
                        rfl

theorem cell23_4945354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_4945354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945354 prefixEnd_4945354 := by exact prefixLift 4945354
  have htrace : WordTrace (prefixWord ++ tailWord_4945354) baseStart_4945354 baseEnd_4945354 := by
    simpa [prefixWord, tailWord_4945354, baseEnd_4945354] using wordTrace_append hprefix tailTrace_4945354
  have hstable : (prefixWord ++ tailWord_4945354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945354).length < 2 ^ (prefixWord ++ tailWord_4945354).sum := by decide
  have hdescent : baseEnd_4945354 < baseStart_4945354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945367 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 1, 8, 2]
def baseStart_4945367 : Nat := 118140960795 + 4945367 * 2 ^ 59
def prefixEnd_4945367 : Nat := 4983230072969 + 3 ^ 40 * 4945367 * 2
def baseEnd_4945367 : Nat := 2539350283883457962569177

theorem tailTrace_4945367 : CollatzResearch.WordTrace tailWord_4945367 prefixEnd_4945367 2539350283883457962569177 := by
  unfold tailWord_4945367
  simp only [CollatzResearch.WordTrace]
  refine ⟨180372352674787435286554355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120248235116524956857702903 180372352674787435286554355)
  ·
    refine ⟨270558529012181152929831533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180372352674787435286554355 270558529012181152929831533)
    ·
      refine ⟨101459448379567932348686825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270558529012181152929831533 101459448379567932348686825)
      ·
        refine ⟨76094586284675949261515119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101459448379567932348686825 76094586284675949261515119)
        ·
          refine ⟨114141879427013923892272679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76094586284675949261515119 114141879427013923892272679)
          ·
            refine ⟨171212819140520885838409019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114141879427013923892272679 171212819140520885838409019)
            ·
              refine ⟨256819228710781328757613529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171212819140520885838409019 256819228710781328757613529)
              ·
                refine ⟨192614421533085996568210147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256819228710781328757613529 192614421533085996568210147)
                ·
                  refine ⟨288921632299628994852315221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192614421533085996568210147 288921632299628994852315221)
                  ·
                    refine ⟨3385800378511277283425569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 288921632299628994852315221 3385800378511277283425569)
                    ·
                      refine ⟨2539350283883457962569177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3385800378511277283425569 2539350283883457962569177)
                      ·
                        rfl

theorem cell23_4945367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_4945367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945367 prefixEnd_4945367 := by exact prefixLift 4945367
  have htrace : WordTrace (prefixWord ++ tailWord_4945367) baseStart_4945367 baseEnd_4945367 := by
    simpa [prefixWord, tailWord_4945367, baseEnd_4945367] using wordTrace_append hprefix tailTrace_4945367
  have hstable : (prefixWord ++ tailWord_4945367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945367).length < 2 ^ (prefixWord ++ tailWord_4945367).sum := by decide
  have hdescent : baseEnd_4945367 < baseStart_4945367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945387 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 3]
def baseStart_4945387 : Nat := 118140960795 + 4945387 * 2 ^ 59
def prefixEnd_4945387 : Nat := 4983230072969 + 3 ^ 40 * 4945387 * 2
def baseEnd_4945387 : Nat := 2539360553496547884319085

theorem tailTrace_4945387 : CollatzResearch.WordTrace tailWord_4945387 prefixEnd_4945387 2539360553496547884319085 := by
  unfold tailWord_4945387
  simp only [CollatzResearch.WordTrace]
  refine ⟨180373082134714978702282415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120248721423143319134854943 180373082134714978702282415)
  ·
    refine ⟨270559623202072468053423623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180373082134714978702282415 270559623202072468053423623)
    ·
      refine ⟨405839434803108702080135435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270559623202072468053423623 405839434803108702080135435)
      ·
        refine ⟨608759152204663053120203153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405839434803108702080135435 608759152204663053120203153)
        ·
          refine ⟨456569364153497289840152365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 608759152204663053120203153 456569364153497289840152365)
          ·
            refine ⟨171213511557561483690057137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 456569364153497289840152365 171213511557561483690057137)
            ·
              refine ⟨128410133668171112767542853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171213511557561483690057137 128410133668171112767542853)
              ·
                refine ⟨24076900062782083643914285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128410133668171112767542853 24076900062782083643914285)
                ·
                  refine ⟨9028837523543281366467857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24076900062782083643914285 9028837523543281366467857)
                  ·
                    refine ⟨6771628142657461024850893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9028837523543281366467857 6771628142657461024850893)
                    ·
                      refine ⟨2539360553496547884319085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6771628142657461024850893 2539360553496547884319085)
                      ·
                        rfl

theorem cell23_4945387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 3].length) (baseStart_4945387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945387 prefixEnd_4945387 := by exact prefixLift 4945387
  have htrace : WordTrace (prefixWord ++ tailWord_4945387) baseStart_4945387 baseEnd_4945387 := by
    simpa [prefixWord, tailWord_4945387, baseEnd_4945387] using wordTrace_append hprefix tailTrace_4945387
  have hstable : (prefixWord ++ tailWord_4945387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945387).length < 2 ^ (prefixWord ++ tailWord_4945387).sum := by decide
  have hdescent : baseEnd_4945387 < baseStart_4945387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945394 : List Nat := [3, 2, 1, 4, 1, 1, 3, 1, 1, 6]
def baseStart_4945394 : Nat := 118140960795 + 4945394 * 2 ^ 59
def prefixEnd_4945394 : Nat := 4983230072969 + 3 ^ 40 * 4945394 * 2
def baseEnd_4945394 : Nat := 846454715953709785643851

theorem tailTrace_4945394 : CollatzResearch.WordTrace tailWord_4945394 prefixEnd_4945394 846454715953709785643851 := by
  unfold tailWord_4945394
  simp only [CollatzResearch.WordTrace]
  refine ⟨45093334361422404724446809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120248891630459745931858157 45093334361422404724446809)
  ·
    refine ⟨33820000771066803543335107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45093334361422404724446809 33820000771066803543335107)
    ·
      refine ⟨50730001156600205315002661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33820000771066803543335107 50730001156600205315002661)
      ·
        refine ⟨9511875216862538496562999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50730001156600205315002661 9511875216862538496562999)
        ·
          refine ⟨14267812825293807744844499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9511875216862538496562999 14267812825293807744844499)
          ·
            refine ⟨21401719237940711617266749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14267812825293807744844499 21401719237940711617266749)
            ·
              refine ⟨8025644714227766856475031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21401719237940711617266749 8025644714227766856475031)
              ·
                refine ⟨12038467071341650284712547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8025644714227766856475031 12038467071341650284712547)
                ·
                  refine ⟨18057700607012475427068821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12038467071341650284712547 18057700607012475427068821)
                  ·
                    refine ⟨846454715953709785643851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18057700607012475427068821 846454715953709785643851)
                    ·
                      rfl

theorem cell23_4945394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_4945394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945394 prefixEnd_4945394 := by exact prefixLift 4945394
  have htrace : WordTrace (prefixWord ++ tailWord_4945394) baseStart_4945394 baseEnd_4945394 := by
    simpa [prefixWord, tailWord_4945394, baseEnd_4945394] using wordTrace_append hprefix tailTrace_4945394
  have hstable : (prefixWord ++ tailWord_4945394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945394).length < 2 ^ (prefixWord ++ tailWord_4945394).sum := by decide
  have hdescent : baseEnd_4945394 < baseStart_4945394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945404 : List Nat := [2, 2, 2, 1, 2, 1, 3, 4, 1, 2, 3]
def baseStart_4945404 : Nat := 118140960795 + 4945404 * 2 ^ 59
def prefixEnd_4945404 : Nat := 4983230072969 + 3 ^ 40 * 4945404 * 2
def baseEnd_4945404 : Nat := 2539369282667674317806507

theorem tailTrace_4945404 : CollatzResearch.WordTrace tailWord_4945404 prefixEnd_4945404 2539369282667674317806507 := by
  unfold tailWord_4945404
  simp only [CollatzResearch.WordTrace]
  refine ⟨90186851087826695302825633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120249134783768927070434177 90186851087826695302825633)
  ·
    refine ⟨67640138315870021477119225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90186851087826695302825633 67640138315870021477119225)
    ·
      refine ⟨50730103736902516107839419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67640138315870021477119225 50730103736902516107839419)
      ·
        refine ⟨76095155605353774161759129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50730103736902516107839419 76095155605353774161759129)
        ·
          refine ⟨57071366704015330621319347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76095155605353774161759129 57071366704015330621319347)
          ·
            refine ⟨85607050056022995931979021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57071366704015330621319347 85607050056022995931979021)
            ·
              refine ⟨32102643771008623474492133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85607050056022995931979021 32102643771008623474492133)
              ·
                refine ⟨6019245707064116901467275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32102643771008623474492133 6019245707064116901467275)
                ·
                  refine ⟨9028868560596175352200913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6019245707064116901467275 9028868560596175352200913)
                  ·
                    refine ⟨6771651420447131514150685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9028868560596175352200913 6771651420447131514150685)
                    ·
                      refine ⟨2539369282667674317806507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6771651420447131514150685 2539369282667674317806507)
                      ·
                        rfl

theorem cell23_4945404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_4945404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945404 prefixEnd_4945404 := by exact prefixLift 4945404
  have htrace : WordTrace (prefixWord ++ tailWord_4945404) baseStart_4945404 baseEnd_4945404 := by
    simpa [prefixWord, tailWord_4945404, baseEnd_4945404] using wordTrace_append hprefix tailTrace_4945404
  have hstable : (prefixWord ++ tailWord_4945404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945404).length < 2 ^ (prefixWord ++ tailWord_4945404).sum := by decide
  have hdescent : baseEnd_4945404 < baseStart_4945404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945412 : List Nat := [2, 3, 2, 3, 3, 1, 1, 3, 1, 1, 3]
def baseStart_4945412 : Nat := 118140960795 + 4945412 * 2 ^ 59
def prefixEnd_4945412 : Nat := 4983230072969 + 3 ^ 40 * 4945412 * 2
def baseEnd_4945412 : Nat := 2539373390512910286506471

theorem tailTrace_4945412 : CollatzResearch.WordTrace tailWord_4945412 prefixEnd_4945412 2539373390512910286506471 := by
  unfold tailWord_4945412
  simp only [CollatzResearch.WordTrace]
  refine ⟨90186996979812203985971245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120249329306416271981294993 90186996979812203985971245)
  ·
    refine ⟨33820123867429576494739217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90186996979812203985971245 33820123867429576494739217)
    ·
      refine ⟨25365092900572182371054413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33820123867429576494739217 25365092900572182371054413)
      ·
        refine ⟨9511909837714568389145405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25365092900572182371054413 9511909837714568389145405)
        ·
          refine ⟨3566966189142963145929527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9511909837714568389145405 3566966189142963145929527)
          ·
            refine ⟨5350449283714444718894291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3566966189142963145929527 5350449283714444718894291)
            ·
              refine ⟨8025673925571667078341437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5350449283714444718894291 8025673925571667078341437)
              ·
                refine ⟨3009627722089375154378039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8025673925571667078341437 3009627722089375154378039)
                ·
                  refine ⟨4514441583134062731567059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3009627722089375154378039 4514441583134062731567059)
                  ·
                    refine ⟨6771662374701094097350589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4514441583134062731567059 6771662374701094097350589)
                    ·
                      refine ⟨2539373390512910286506471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6771662374701094097350589 2539373390512910286506471)
                      ·
                        rfl

theorem cell23_4945412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_4945412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945412 prefixEnd_4945412 := by exact prefixLift 4945412
  have htrace : WordTrace (prefixWord ++ tailWord_4945412) baseStart_4945412 baseEnd_4945412 := by
    simpa [prefixWord, tailWord_4945412, baseEnd_4945412] using wordTrace_append hprefix tailTrace_4945412
  have hstable : (prefixWord ++ tailWord_4945412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945412).length < 2 ^ (prefixWord ++ tailWord_4945412).sum := by decide
  have hdescent : baseEnd_4945412 < baseStart_4945412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945417 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 3, 3, 3]
def baseStart_4945417 : Nat := 118140960795 + 4945417 * 2 ^ 59
def prefixEnd_4945417 : Nat := 4983230072969 + 3 ^ 40 * 4945417 * 2
def baseEnd_4945417 : Nat := 2539375957916182766943947

theorem tailTrace_4945417 : CollatzResearch.WordTrace tailWord_4945417 prefixEnd_4945417 2539375957916182766943947 := by
  unfold tailWord_4945417
  simp only [CollatzResearch.WordTrace]
  refine ⟨180374176324606293825874505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120249450883070862550583003 180374176324606293825874505)
  ·
    refine ⟨135280632243454720369405879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180374176324606293825874505 135280632243454720369405879)
    ·
      refine ⟨202920948365182080554108819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135280632243454720369405879 202920948365182080554108819)
      ·
        refine ⟨304381422547773120831163229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202920948365182080554108819 304381422547773120831163229)
        ·
          refine ⟨114143033455414920311686211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 304381422547773120831163229 114143033455414920311686211)
          ·
            refine ⟨171214550183122380467529317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114143033455414920311686211 171214550183122380467529317)
            ·
              refine ⟨32102728159335446337661747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171214550183122380467529317 32102728159335446337661747)
              ·
                refine ⟨48154092239003169506492621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32102728159335446337661747 48154092239003169506492621)
                ·
                  refine ⟨18057784589626188564934733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48154092239003169506492621 18057784589626188564934733)
                  ·
                    refine ⟨6771669221109820711850525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18057784589626188564934733 6771669221109820711850525)
                    ·
                      refine ⟨2539375957916182766943947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6771669221109820711850525 2539375957916182766943947)
                      ·
                        rfl

theorem cell23_4945417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 3, 3].length) (baseStart_4945417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945417 prefixEnd_4945417 := by exact prefixLift 4945417
  have htrace : WordTrace (prefixWord ++ tailWord_4945417) baseStart_4945417 baseEnd_4945417 := by
    simpa [prefixWord, tailWord_4945417, baseEnd_4945417] using wordTrace_append hprefix tailTrace_4945417
  have hstable : (prefixWord ++ tailWord_4945417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945417).length < 2 ^ (prefixWord ++ tailWord_4945417).sum := by decide
  have hdescent : baseEnd_4945417 < baseStart_4945417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945437 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 2, 7]
def baseStart_4945437 : Nat := 118140960795 + 4945437 * 2 ^ 59
def prefixEnd_4945437 : Nat := 4983230072969 + 3 ^ 40 * 4945437 * 2
def baseEnd_4945437 : Nat := 846462075843090896231285

theorem tailTrace_4945437 : CollatzResearch.WordTrace tailWord_4945437 prefixEnd_4945437 846462075843090896231285 := by
  unfold tailWord_4945437
  simp only [CollatzResearch.WordTrace]
  refine ⟨180374905784533837241602565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120249937189689224827735043 180374905784533837241602565)
  ·
    refine ⟨33820294834600094482800481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180374905784533837241602565 33820294834600094482800481)
    ·
      refine ⟨25365221125950070862100361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33820294834600094482800481 25365221125950070862100361)
      ·
        refine ⟨19023915844462553146575271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25365221125950070862100361 19023915844462553146575271)
        ·
          refine ⟨28535873766693829719862907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19023915844462553146575271 28535873766693829719862907)
          ·
            refine ⟨42803810650040744579794361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28535873766693829719862907 42803810650040744579794361)
            ·
              refine ⟨32102857987530558434845771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42803810650040744579794361 32102857987530558434845771)
              ·
                refine ⟨48154286981295837652268657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32102857987530558434845771 48154286981295837652268657)
                ·
                  refine ⟨36115715235971878239201493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48154286981295837652268657 36115715235971878239201493)
                  ·
                    refine ⟨846462075843090896231285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36115715235971878239201493 846462075843090896231285)
                    ·
                      rfl

theorem cell23_4945437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_4945437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945437 prefixEnd_4945437 := by exact prefixLift 4945437
  have htrace : WordTrace (prefixWord ++ tailWord_4945437) baseStart_4945437 baseEnd_4945437 := by
    simpa [prefixWord, tailWord_4945437, baseEnd_4945437] using wordTrace_append hprefix tailTrace_4945437
  have hstable : (prefixWord ++ tailWord_4945437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945437).length < 2 ^ (prefixWord ++ tailWord_4945437).sum := by decide
  have hdescent : baseEnd_4945437 < baseStart_4945437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945461 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 3, 3, 2]
def baseStart_4945461 : Nat := 118140960795 + 4945461 * 2 ^ 59
def prefixEnd_4945461 : Nat := 4983230072969 + 3 ^ 40 * 4945461 * 2
def baseEnd_4945461 : Nat := 2539398551064980594793745

theorem tailTrace_4945461 : CollatzResearch.WordTrace tailWord_4945461 prefixEnd_4945461 2539398551064980594793745 := by
  unfold tailWord_4945461
  simp only [CollatzResearch.WordTrace]
  refine ⟨180375781136446889340476237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120250520757631259560317491 180375781136446889340476237)
  ·
    refine ⟨67640917926167583502678589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180375781136446889340476237 67640917926167583502678589)
    ·
      refine ⟨25365344222312843813504471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67640917926167583502678589 25365344222312843813504471)
      ·
        refine ⟨38048016333469265720256707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25365344222312843813504471 38048016333469265720256707)
        ·
          refine ⟨57072024500203898580385061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38048016333469265720256707 57072024500203898580385061)
          ·
            refine ⟨10701004593788230983822199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57072024500203898580385061 10701004593788230983822199)
            ·
              refine ⟨16051506890682346475733299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10701004593788230983822199 16051506890682346475733299)
              ·
                refine ⟨24077260336023519713599949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16051506890682346475733299 24077260336023519713599949)
                ·
                  refine ⟨9028972626008819892599981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24077260336023519713599949 9028972626008819892599981)
                  ·
                    refine ⟨3385864734753307459724993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9028972626008819892599981 3385864734753307459724993)
                    ·
                      refine ⟨2539398551064980594793745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3385864734753307459724993 2539398551064980594793745)
                      ·
                        rfl

theorem cell23_4945461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_4945461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945461 prefixEnd_4945461 := by exact prefixLift 4945461
  have htrace : WordTrace (prefixWord ++ tailWord_4945461) baseStart_4945461 baseEnd_4945461 := by
    simpa [prefixWord, tailWord_4945461, baseEnd_4945461] using wordTrace_append hprefix tailTrace_4945461
  have hstable : (prefixWord ++ tailWord_4945461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945461).length < 2 ^ (prefixWord ++ tailWord_4945461).sum := by decide
  have hdescent : baseEnd_4945461 < baseStart_4945461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945477 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 2, 1, 5]
def baseStart_4945477 : Nat := 118140960795 + 4945477 * 2 ^ 59
def prefixEnd_4945477 : Nat := 4983230072969 + 3 ^ 40 * 4945477 * 2
def baseEnd_4945477 : Nat := 2539406766755452532193671

theorem tailTrace_4945477 : CollatzResearch.WordTrace tailWord_4945477 prefixEnd_4945477 2539406766755452532193671 := by
  unfold tailWord_4945477
  simp only [CollatzResearch.WordTrace]
  refine ⟨180376364704388924073058685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120250909802925949382039123 180376364704388924073058685)
  ·
    refine ⟨67641136764145846527397007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180376364704388924073058685 67641136764145846527397007)
    ·
      refine ⟨101461705146218769791095511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67641136764145846527397007 101461705146218769791095511)
      ·
        refine ⟨152192557719328154686643267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101461705146218769791095511 152192557719328154686643267)
        ·
          refine ⟨228288836578992232029964901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152192557719328154686643267 228288836578992232029964901)
          ·
            refine ⟨42804156858561043505618419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228288836578992232029964901 42804156858561043505618419)
            ·
              refine ⟨64206235287841565258427629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42804156858561043505618419 64206235287841565258427629)
              ·
                refine ⟨24077338232940586971910361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64206235287841565258427629 24077338232940586971910361)
                ·
                  refine ⟨18058003674705440228932771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24077338232940586971910361 18058003674705440228932771)
                  ·
                    refine ⟨27087005512058160343399157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18058003674705440228932771 27087005512058160343399157)
                    ·
                      refine ⟨2539406766755452532193671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27087005512058160343399157 2539406766755452532193671)
                      ·
                        rfl

theorem cell23_4945477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_4945477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945477 prefixEnd_4945477 := by exact prefixLift 4945477
  have htrace : WordTrace (prefixWord ++ tailWord_4945477) baseStart_4945477 baseEnd_4945477 := by
    simpa [prefixWord, tailWord_4945477, baseEnd_4945477] using wordTrace_append hprefix tailTrace_4945477
  have hstable : (prefixWord ++ tailWord_4945477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945477).length < 2 ^ (prefixWord ++ tailWord_4945477).sum := by decide
  have hdescent : baseEnd_4945477 < baseStart_4945477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945485 : List Nat := [1, 6, 1, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_4945485 : Nat := 118140960795 + 4945485 * 2 ^ 59
def prefixEnd_4945485 : Nat := 4983230072969 + 3 ^ 40 * 4945485 * 2
def baseEnd_4945485 : Nat := 2539410874600688500893635

theorem tailTrace_4945485 : CollatzResearch.WordTrace tailWord_4945485 prefixEnd_4945485 2539410874600688500893635 := by
  unfold tailWord_4945485
  simp only [CollatzResearch.WordTrace]
  refine ⟨180376656488359941439349909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120251104325573294292899939 180376656488359941439349909)
  ·
    refine ⟨8455155772891872254969527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 180376656488359941439349909 8455155772891872254969527)
    ·
      refine ⟨12682733659337808382454291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8455155772891872254969527 12682733659337808382454291)
      ·
        refine ⟨19024100489006712573681437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12682733659337808382454291 19024100489006712573681437)
        ·
          refine ⟨7134037683377517215130539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19024100489006712573681437 7134037683377517215130539)
          ·
            refine ⟨10701056525066275822695809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7134037683377517215130539 10701056525066275822695809)
            ·
              refine ⟨8025792393799706867021857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10701056525066275822695809 8025792393799706867021857)
              ·
                refine ⟨6019344295349780150266393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8025792393799706867021857 6019344295349780150266393)
                ·
                  refine ⟨4514508221512335112699795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6019344295349780150266393 4514508221512335112699795)
                  ·
                    refine ⟨6771762332268502669049693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4514508221512335112699795 6771762332268502669049693)
                    ·
                      refine ⟨2539410874600688500893635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6771762332268502669049693 2539410874600688500893635)
                      ·
                        rfl

theorem cell23_4945485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_4945485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945485 prefixEnd_4945485 := by exact prefixLift 4945485
  have htrace : WordTrace (prefixWord ++ tailWord_4945485) baseStart_4945485 baseEnd_4945485 := by
    simpa [prefixWord, tailWord_4945485, baseEnd_4945485] using wordTrace_append hprefix tailTrace_4945485
  have hstable : (prefixWord ++ tailWord_4945485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945485).length < 2 ^ (prefixWord ++ tailWord_4945485).sum := by decide
  have hdescent : baseEnd_4945485 < baseStart_4945485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945487 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 4]
def baseStart_4945487 : Nat := 118140960795 + 4945487 * 2 ^ 59
def prefixEnd_4945487 : Nat := 4983230072969 + 3 ^ 40 * 4945487 * 2
def baseEnd_4945487 : Nat := 2539411901561997493068625

theorem tailTrace_4945487 : CollatzResearch.WordTrace tailWord_4945487 prefixEnd_4945487 2539411901561997493068625 := by
  unfold tailWord_4945487
  simp only [CollatzResearch.WordTrace]
  refine ⟨180376729434352695780922715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120251152956235130520615143 180376729434352695780922715)
  ·
    refine ⟨270565094151529043671384073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180376729434352695780922715 270565094151529043671384073)
    ·
      refine ⟨202923820613646782753538055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270565094151529043671384073 202923820613646782753538055)
      ·
        refine ⟨304385730920470174130307083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202923820613646782753538055 304385730920470174130307083)
        ·
          refine ⟨456578596380705261195460625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304385730920470174130307083 456578596380705261195460625)
          ·
            refine ⟨342433947285528945896595469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 456578596380705261195460625 342433947285528945896595469)
            ·
              refine ⟨128412730232073354711223301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 342433947285528945896595469 128412730232073354711223301)
              ·
                refine ⟨24077386918513754008354369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128412730232073354711223301 24077386918513754008354369)
                ·
                  refine ⟨18058040188885315506265777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24077386918513754008354369 18058040188885315506265777)
                  ·
                    refine ⟨13543530141663986629699333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18058040188885315506265777 13543530141663986629699333)
                    ·
                      refine ⟨2539411901561997493068625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13543530141663986629699333 2539411901561997493068625)
                      ·
                        rfl

theorem cell23_4945487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 4].length) (baseStart_4945487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945487 prefixEnd_4945487 := by exact prefixLift 4945487
  have htrace : WordTrace (prefixWord ++ tailWord_4945487) baseStart_4945487 baseEnd_4945487 := by
    simpa [prefixWord, tailWord_4945487, baseEnd_4945487] using wordTrace_append hprefix tailTrace_4945487
  have hstable : (prefixWord ++ tailWord_4945487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945487).length < 2 ^ (prefixWord ++ tailWord_4945487).sum := by decide
  have hdescent : baseEnd_4945487 < baseStart_4945487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945508 : List Nat := [2, 3, 1, 1, 2, 3, 2, 3, 2, 2, 2]
def baseStart_4945508 : Nat := 118140960795 + 4945508 * 2 ^ 59
def prefixEnd_4945508 : Nat := 4983230072969 + 3 ^ 40 * 4945508 * 2
def baseEnd_4945508 : Nat := 2539422684655741910906029

theorem tailTrace_4945508 : CollatzResearch.WordTrace tailWord_4945508 prefixEnd_4945508 2539422684655741910906029 := by
  unfold tailWord_4945508
  simp only [CollatzResearch.WordTrace]
  refine ⟨90188747683638308183718589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120251663578184410911624785 90188747683638308183718589)
  ·
    refine ⟨33820780381364365568894471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90188747683638308183718589 33820780381364365568894471)
    ·
      refine ⟨50731170572046548353341707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33820780381364365568894471 50731170572046548353341707)
      ·
        refine ⟨76096755858069822530012561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50731170572046548353341707 76096755858069822530012561)
        ·
          refine ⟨57072566893552366897509421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76096755858069822530012561 57072566893552366897509421)
          ·
            refine ⟨21402212585082137586566033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57072566893552366897509421 21402212585082137586566033)
            ·
              refine ⟨16051659438811603189924525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21402212585082137586566033 16051659438811603189924525)
              ·
                refine ⟨6019372289554351196221697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16051659438811603189924525 6019372289554351196221697)
                ·
                  refine ⟨4514529217165763397166273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6019372289554351196221697 4514529217165763397166273)
                  ·
                    refine ⟨3385896912874322547874705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4514529217165763397166273 3385896912874322547874705)
                    ·
                      refine ⟨2539422684655741910906029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3385896912874322547874705 2539422684655741910906029)
                      ·
                        rfl

theorem cell23_4945508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_4945508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945508 prefixEnd_4945508 := by exact prefixLift 4945508
  have htrace : WordTrace (prefixWord ++ tailWord_4945508) baseStart_4945508 baseEnd_4945508 := by
    simpa [prefixWord, tailWord_4945508, baseEnd_4945508] using wordTrace_append hprefix tailTrace_4945508
  have hstable : (prefixWord ++ tailWord_4945508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945508).length < 2 ^ (prefixWord ++ tailWord_4945508).sum := by decide
  have hdescent : baseEnd_4945508 < baseStart_4945508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945514 : List Nat := [3, 1, 3, 2, 1, 3, 1, 2, 7]
def baseStart_4945514 : Nat := 118140960795 + 4945514 * 2 ^ 59
def prefixEnd_4945514 : Nat := 4983230072969 + 3 ^ 40 * 4945514 * 2
def baseEnd_4945514 : Nat := 282158418393296543047889

theorem tailTrace_4945514 : CollatzResearch.WordTrace tailWord_4945514 prefixEnd_4945514 282158418393296543047889 := by
  unfold tailWord_4945514
  simp only [CollatzResearch.WordTrace]
  refine ⟨45094428551313719848038899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120251809470169919594770397 45094428551313719848038899)
  ·
    refine ⟨67641642826970579772058349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45094428551313719848038899 67641642826970579772058349)
    ·
      refine ⟨25365616060113967414521881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67641642826970579772058349 25365616060113967414521881)
      ·
        refine ⟨19024212045085475560891411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25365616060113967414521881 19024212045085475560891411)
        ·
          refine ⟨28536318067628213341337117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19024212045085475560891411 28536318067628213341337117)
          ·
            refine ⟨10701119275360580003001419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28536318067628213341337117 10701119275360580003001419)
            ·
              refine ⟨16051678913040870004502129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10701119275360580003001419 16051678913040870004502129)
              ·
                refine ⟨12038759184780652503376597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16051678913040870004502129 12038759184780652503376597)
                ·
                  refine ⟨282158418393296543047889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12038759184780652503376597 282158418393296543047889)
                  ·
                    rfl

theorem cell23_4945514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 7].length) (baseStart_4945514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945514 prefixEnd_4945514 := by exact prefixLift 4945514
  have htrace : WordTrace (prefixWord ++ tailWord_4945514) baseStart_4945514 baseEnd_4945514 := by
    simpa [prefixWord, tailWord_4945514, baseEnd_4945514] using wordTrace_append hprefix tailTrace_4945514
  have hstable : (prefixWord ++ tailWord_4945514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945514).length < 2 ^ (prefixWord ++ tailWord_4945514).sum := by decide
  have hdescent : baseEnd_4945514 < baseStart_4945514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945581 : List Nat := [1, 5, 2, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_4945581 : Nat := 118140960795 + 4945581 * 2 ^ 59
def prefixEnd_4945581 : Nat := 4983230072969 + 3 ^ 40 * 4945581 * 2
def baseEnd_4945581 : Nat := 2539460168743520125293193

theorem tailTrace_4945581 : CollatzResearch.WordTrace tailWord_4945581 prefixEnd_4945581 2539460168743520125293193 := by
  unfold tailWord_4945581
  simp only [CollatzResearch.WordTrace]
  refine ⟨180380157896012149834844597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120253438597341433223229731 180380157896012149834844597)
  ·
    refine ⟨16910639802751139047016681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 180380157896012149834844597 16910639802751139047016681)
    ·
      refine ⟨12682979852063354285262511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16910639802751139047016681 12682979852063354285262511)
      ·
        refine ⟨19024469778095031427893767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12682979852063354285262511 19024469778095031427893767)
        ·
          refine ⟨28536704667142547141840651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19024469778095031427893767 28536704667142547141840651)
          ·
            refine ⟨42805057000713820712760977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28536704667142547141840651 42805057000713820712760977)
            ·
              refine ⟨32103792750535365534570733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42805057000713820712760977 32103792750535365534570733)
              ·
                refine ⟨12038922281450762075464025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32103792750535365534570733 12038922281450762075464025)
                ·
                  refine ⟨9029191711088071556598019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12038922281450762075464025 9029191711088071556598019)
                  ·
                    refine ⟨13543787566632107334897029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9029191711088071556598019 13543787566632107334897029)
                    ·
                      refine ⟨2539460168743520125293193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13543787566632107334897029 2539460168743520125293193)
                      ·
                        rfl

theorem cell23_4945581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_4945581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945581 prefixEnd_4945581 := by exact prefixLift 4945581
  have htrace : WordTrace (prefixWord ++ tailWord_4945581) baseStart_4945581 baseEnd_4945581 := by
    simpa [prefixWord, tailWord_4945581, baseEnd_4945581] using wordTrace_append hprefix tailTrace_4945581
  have hstable : (prefixWord ++ tailWord_4945581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945581).length < 2 ^ (prefixWord ++ tailWord_4945581).sum := by decide
  have hdescent : baseEnd_4945581 < baseStart_4945581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945582 : List Nat := [4, 1, 4, 1, 3, 1, 1, 3, 5]
def baseStart_4945582 : Nat := 118140960795 + 4945582 * 2 ^ 59
def prefixEnd_4945582 : Nat := 4983230072969 + 3 ^ 40 * 4945582 * 2
def baseEnd_4945582 : Nat := 282162298024908291264521

theorem tailTrace_4945582 : CollatzResearch.WordTrace tailWord_4945582 prefixEnd_4945582 282162298024908291264521 := by
  unfold tailWord_4945582
  simp only [CollatzResearch.WordTrace]
  refine ⟨22547524296126065875703875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120253462912672351337087333 22547524296126065875703875)
  ·
    refine ⟨33821286444189098813555813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22547524296126065875703875 33821286444189098813555813)
    ·
      refine ⟨6341491208285456027541715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33821286444189098813555813 6341491208285456027541715)
      ·
        refine ⟨9512236812428184041312573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6341491208285456027541715 9512236812428184041312573)
        ·
          refine ⟨3567088804660569015492215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9512236812428184041312573 3567088804660569015492215)
          ·
            refine ⟨5350633206990853523238323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3567088804660569015492215 5350633206990853523238323)
            ·
              refine ⟨8025949810486280284857485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5350633206990853523238323 8025949810486280284857485)
              ·
                refine ⟨3009731178932355106821557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8025949810486280284857485 3009731178932355106821557)
                ·
                  refine ⟨282162298024908291264521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3009731178932355106821557 282162298024908291264521)
                  ·
                    rfl

theorem cell23_4945582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_4945582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945582 prefixEnd_4945582 := by exact prefixLift 4945582
  have htrace : WordTrace (prefixWord ++ tailWord_4945582) baseStart_4945582 baseEnd_4945582 := by
    simpa [prefixWord, tailWord_4945582, baseEnd_4945582] using wordTrace_append hprefix tailTrace_4945582
  have hstable : (prefixWord ++ tailWord_4945582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945582).length < 2 ^ (prefixWord ++ tailWord_4945582).sum := by decide
  have hdescent : baseEnd_4945582 < baseStart_4945582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945584 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 3]
def baseStart_4945584 : Nat := 118140960795 + 4945584 * 2 ^ 59
def prefixEnd_4945584 : Nat := 4983230072969 + 3 ^ 40 * 4945584 * 2
def baseEnd_4945584 : Nat := 2539461709185483613555679

theorem tailTrace_4945584 : CollatzResearch.WordTrace tailWord_4945584 prefixEnd_4945584 2539461709185483613555679 := by
  unfold tailWord_4945584
  simp only [CollatzResearch.WordTrace]
  refine ⟨90190133657500640673601903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120253511543334187564802537 90190133657500640673601903)
  ·
    refine ⟨135285200486250961010402855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90190133657500640673601903 135285200486250961010402855)
    ·
      refine ⟨202927800729376441515604283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135285200486250961010402855 202927800729376441515604283)
      ·
        refine ⟨304391701094064662273406425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202927800729376441515604283 304391701094064662273406425)
        ·
          refine ⟨228293775820548496705054819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304391701094064662273406425 228293775820548496705054819)
          ·
            refine ⟨342440663730822745057582229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228293775820548496705054819 342440663730822745057582229)
            ·
              refine ⟨16051906112382316174574167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 342440663730822745057582229 16051906112382316174574167)
              ·
                refine ⟨24077859168573474261861251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16051906112382316174574167 24077859168573474261861251)
                ·
                  refine ⟨36116788752860211392791877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24077859168573474261861251 36116788752860211392791877)
                  ·
                    refine ⟨6771897891161289636148477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36116788752860211392791877 6771897891161289636148477)
                    ·
                      refine ⟨2539461709185483613555679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6771897891161289636148477 2539461709185483613555679)
                      ·
                        rfl

theorem cell23_4945584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 3].length) (baseStart_4945584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945584 prefixEnd_4945584 := by exact prefixLift 4945584
  have htrace : WordTrace (prefixWord ++ tailWord_4945584) baseStart_4945584 baseEnd_4945584 := by
    simpa [prefixWord, tailWord_4945584, baseEnd_4945584] using wordTrace_append hprefix tailTrace_4945584
  have hstable : (prefixWord ++ tailWord_4945584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945584).length < 2 ^ (prefixWord ++ tailWord_4945584).sum := by decide
  have hdescent : baseEnd_4945584 < baseStart_4945584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945587 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 10]
def baseStart_4945587 : Nat := 118140960795 + 4945587 * 2 ^ 59
def prefixEnd_4945587 : Nat := 4983230072969 + 3 ^ 40 * 4945587 * 2
def baseEnd_4945587 : Nat := 282162583291938566868685

theorem tailTrace_4945587 : CollatzResearch.WordTrace tailWord_4945587 prefixEnd_4945587 282162583291938566868685 := by
  unfold tailWord_4945587
  simp only [CollatzResearch.WordTrace]
  refine ⟨180380376733990412859563015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120253584489326941906375343 180380376733990412859563015)
  ·
    refine ⟨270570565100985619289344523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180380376733990412859563015 270570565100985619289344523)
    ·
      refine ⟨405855847651478428934016785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270570565100985619289344523 405855847651478428934016785)
      ·
        refine ⟨304391885738608821700512589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 405855847651478428934016785 304391885738608821700512589)
        ·
          refine ⟨114146957151978308137692221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 304391885738608821700512589 114146957151978308137692221)
          ·
            refine ⟨42805108931991865551634583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114146957151978308137692221 42805108931991865551634583)
            ·
              refine ⟨64207663397987798327451875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42805108931991865551634583 64207663397987798327451875)
              ·
                refine ⟨96311495096981697491177813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64207663397987798327451875 96311495096981697491177813)
                ·
                  refine ⟨282162583291938566868685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 96311495096981697491177813 282162583291938566868685)
                  ·
                    rfl

theorem cell23_4945587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 10].length) (baseStart_4945587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945587 prefixEnd_4945587 := by exact prefixLift 4945587
  have htrace : WordTrace (prefixWord ++ tailWord_4945587) baseStart_4945587 baseEnd_4945587 := by
    simpa [prefixWord, tailWord_4945587, baseEnd_4945587] using wordTrace_append hprefix tailTrace_4945587
  have hstable : (prefixWord ++ tailWord_4945587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945587).length < 2 ^ (prefixWord ++ tailWord_4945587).sum := by decide
  have hdescent : baseEnd_4945587 < baseStart_4945587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945604 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 8]
def baseStart_4945604 : Nat := 118140960795 + 4945604 * 2 ^ 59
def prefixEnd_4945604 : Nat := 4983230072969 + 3 ^ 40 * 4945604 * 2
def baseEnd_4945604 : Nat := 282163553199841503922843

theorem tailTrace_4945604 : CollatzResearch.WordTrace tailWord_4945604 prefixEnd_4945604 282163553199841503922843 := by
  unfold tailWord_4945604
  simp only [CollatzResearch.WordTrace]
  refine ⟨90190498387464412381465933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120253997849952549841954577 90190498387464412381465933)
  ·
    refine ⟨33821436895299154643049725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90190498387464412381465933 33821436895299154643049725)
    ·
      refine ⟨12683038835737182991143647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33821436895299154643049725 12683038835737182991143647)
      ·
        refine ⟨19024558253605774486715471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12683038835737182991143647 19024558253605774486715471)
        ·
          refine ⟨28536837380408661730073207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19024558253605774486715471 28536837380408661730073207)
          ·
            refine ⟨42805256070612992595109811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28536837380408661730073207 42805256070612992595109811)
            ·
              refine ⟨64207884105919488892664717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42805256070612992595109811 64207884105919488892664717)
              ·
                refine ⟨24077956539719808334749269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64207884105919488892664717 24077956539719808334749269)
                ·
                  refine ⟨282163553199841503922843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24077956539719808334749269 282163553199841503922843)
                  ·
                    rfl

theorem cell23_4945604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_4945604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945604 prefixEnd_4945604 := by exact prefixLift 4945604
  have htrace : WordTrace (prefixWord ++ tailWord_4945604) baseStart_4945604 baseEnd_4945604 := by
    simpa [prefixWord, tailWord_4945604, baseEnd_4945604] using wordTrace_append hprefix tailTrace_4945604
  have hstable : (prefixWord ++ tailWord_4945604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945604).length < 2 ^ (prefixWord ++ tailWord_4945604).sum := by decide
  have hdescent : baseEnd_4945604 < baseStart_4945604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945631 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 5, 1, 3]
def baseStart_4945631 : Nat := 118140960795 + 4945631 * 2 ^ 59
def prefixEnd_4945631 : Nat := 4983230072969 + 3 ^ 40 * 4945631 * 2
def baseEnd_4945631 : Nat := 2539485842776244929667963

theorem tailTrace_4945631 : CollatzResearch.WordTrace tailWord_4945631 prefixEnd_4945631 2539485842776244929667963 := by
  unfold tailWord_4945631
  simp only [CollatzResearch.WordTrace]
  refine ⟨180381981545831008374164747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120254654363887338916109831 180381981545831008374164747)
  ·
    refine ⟨270572972318746512561247121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180381981545831008374164747 270572972318746512561247121)
    ·
      refine ⟨202929729239059884420935341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270572972318746512561247121 202929729239059884420935341)
      ·
        refine ⟨76098648464647456657850753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202929729239059884420935341 76098648464647456657850753)
        ·
          refine ⟨57073986348485592493388065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76098648464647456657850753 57073986348485592493388065)
          ·
            refine ⟨42805489761364194370041049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57073986348485592493388065 42805489761364194370041049)
            ·
              refine ⟨32104117321023145777530787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42805489761364194370041049 32104117321023145777530787)
              ·
                refine ⟨48156175981534718666296181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32104117321023145777530787 48156175981534718666296181)
                ·
                  refine ⟨4514641498268879874965267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48156175981534718666296181 4514641498268879874965267)
                  ·
                    refine ⟨6771962247403319812447901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4514641498268879874965267 6771962247403319812447901)
                    ·
                      refine ⟨2539485842776244929667963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6771962247403319812447901 2539485842776244929667963)
                      ·
                        rfl

theorem cell23_4945631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_4945631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945631 prefixEnd_4945631 := by exact prefixLift 4945631
  have htrace : WordTrace (prefixWord ++ tailWord_4945631) baseStart_4945631 baseEnd_4945631 := by
    simpa [prefixWord, tailWord_4945631, baseEnd_4945631] using wordTrace_append hprefix tailTrace_4945631
  have hstable : (prefixWord ++ tailWord_4945631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945631).length < 2 ^ (prefixWord ++ tailWord_4945631).sum := by decide
  have hdescent : baseEnd_4945631 < baseStart_4945631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945688 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 5, 2, 2]
def baseStart_4945688 : Nat := 118140960795 + 4945688 * 2 ^ 59
def prefixEnd_4945688 : Nat := 4983230072969 + 3 ^ 40 * 4945688 * 2
def baseEnd_4945688 : Nat := 2539515111173551206655201

theorem tailTrace_4945688 : CollatzResearch.WordTrace tailWord_4945688 prefixEnd_4945688 2539515111173551206655201 := by
  unfold tailWord_4945688
  simp only [CollatzResearch.WordTrace]
  refine ⟨90192030253312253554494859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120256040337749671405993145 90192030253312253554494859)
  ·
    refine ⟨135288045379968380331742289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90192030253312253554494859 135288045379968380331742289)
    ·
      refine ⟨101466034034976285248806717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135288045379968380331742289 101466034034976285248806717)
      ·
        refine ⟨38049762763116106968302519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101466034034976285248806717 38049762763116106968302519)
        ·
          refine ⟨57074644144674160452453779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38049762763116106968302519 57074644144674160452453779)
          ·
            refine ⟨85611966217011240678680669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57074644144674160452453779 85611966217011240678680669)
            ·
              refine ⟨32104487331379215254505251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85611966217011240678680669 32104487331379215254505251)
              ·
                refine ⟨48156730997068822881757877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32104487331379215254505251 48156730997068822881757877)
                ·
                  refine ⟨4514693530975202145164801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48156730997068822881757877 4514693530975202145164801)
                  ·
                    refine ⟨3386020148231401608873601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4514693530975202145164801 3386020148231401608873601)
                    ·
                      refine ⟨2539515111173551206655201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3386020148231401608873601 2539515111173551206655201)
                      ·
                        rfl

theorem cell23_4945688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_4945688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945688 prefixEnd_4945688 := by exact prefixLift 4945688
  have htrace : WordTrace (prefixWord ++ tailWord_4945688) baseStart_4945688 baseEnd_4945688 := by
    simpa [prefixWord, tailWord_4945688, baseEnd_4945688] using wordTrace_append hprefix tailTrace_4945688
  have hstable : (prefixWord ++ tailWord_4945688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945688).length < 2 ^ (prefixWord ++ tailWord_4945688).sum := by decide
  have hdescent : baseEnd_4945688 < baseStart_4945688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945701 : List Nat := [1, 3, 1, 2, 3, 2, 2, 2, 1, 2, 4]
def baseStart_4945701 : Nat := 118140960795 + 4945701 * 2 ^ 59
def prefixEnd_4945701 : Nat := 4983230072969 + 3 ^ 40 * 4945701 * 2
def baseEnd_4945701 : Nat := 2539521786422059655792641

theorem tailTrace_4945701 : CollatzResearch.WordTrace tailWord_4945701 prefixEnd_4945701 2539521786422059655792641 := by
  unfold tailWord_4945701
  simp only [CollatzResearch.WordTrace]
  refine ⟨180384534655577410329212957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120256356437051606886141971 180384534655577410329212957)
  ·
    refine ⟨67644200495841528873454859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180384534655577410329212957 67644200495841528873454859)
    ·
      refine ⟨101466300743762293310182289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67644200495841528873454859 101466300743762293310182289)
      ·
        refine ⟨76099725557821719982636717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101466300743762293310182289 76099725557821719982636717)
        ·
          refine ⟨28537397084183144993488769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76099725557821719982636717 28537397084183144993488769)
          ·
            refine ⟨21403047813137358745116577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28537397084183144993488769 21403047813137358745116577)
            ·
              refine ⟨16052285859853019058837433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21403047813137358745116577 16052285859853019058837433)
              ·
                refine ⟨12039214394889764294128075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16052285859853019058837433 12039214394889764294128075)
                ·
                  refine ⟨18058821592334646441192113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12039214394889764294128075 18058821592334646441192113)
                  ·
                    refine ⟨13544116194250984830894085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18058821592334646441192113 13544116194250984830894085)
                    ·
                      refine ⟨2539521786422059655792641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13544116194250984830894085 2539521786422059655792641)
                      ·
                        rfl

theorem cell23_4945701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_4945701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945701 prefixEnd_4945701 := by exact prefixLift 4945701
  have htrace : WordTrace (prefixWord ++ tailWord_4945701) baseStart_4945701 baseEnd_4945701 := by
    simpa [prefixWord, tailWord_4945701, baseEnd_4945701] using wordTrace_append hprefix tailTrace_4945701
  have hstable : (prefixWord ++ tailWord_4945701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945701).length < 2 ^ (prefixWord ++ tailWord_4945701).sum := by decide
  have hdescent : baseEnd_4945701 < baseStart_4945701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945708 : List Nat := [2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 3]
def baseStart_4945708 : Nat := 118140960795 + 4945708 * 2 ^ 59
def prefixEnd_4945708 : Nat := 4983230072969 + 3 ^ 40 * 4945708 * 2
def baseEnd_4945708 : Nat := 2539525380786641128405109

theorem tailTrace_4945708 : CollatzResearch.WordTrace tailWord_4945708 prefixEnd_4945708 2539525380786641128405109 := by
  unfold tailWord_4945708
  simp only [CollatzResearch.WordTrace]
  refine ⟨90192394983276025262358889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120256526644368033683145185 90192394983276025262358889)
  ·
    refine ⟨67644296237457018946769167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90192394983276025262358889 67644296237457018946769167)
    ·
      refine ⟨101466444356185528420153751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67644296237457018946769167 101466444356185528420153751)
      ·
        refine ⟨152199666534278292630230627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101466444356185528420153751 152199666534278292630230627)
        ·
          refine ⟨228299499801417438945345941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152199666534278292630230627 228299499801417438945345941)
          ·
            refine ⟨10701539053191442450563091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 228299499801417438945345941 10701539053191442450563091)
            ·
              refine ⟨16052308579787163675844637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10701539053191442450563091 16052308579787163675844637)
              ·
                refine ⟨6019615717420186378441739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16052308579787163675844637 6019615717420186378441739)
                ·
                  refine ⟨9029423576130279567662609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6019615717420186378441739 9029423576130279567662609)
                  ·
                    refine ⟨6772067682097709675746957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9029423576130279567662609 6772067682097709675746957)
                    ·
                      refine ⟨2539525380786641128405109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6772067682097709675746957 2539525380786641128405109)
                      ·
                        rfl

theorem cell23_4945708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 3].length) (baseStart_4945708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945708 prefixEnd_4945708 := by exact prefixLift 4945708
  have htrace : WordTrace (prefixWord ++ tailWord_4945708) baseStart_4945708 baseEnd_4945708 := by
    simpa [prefixWord, tailWord_4945708, baseEnd_4945708] using wordTrace_append hprefix tailTrace_4945708
  have hstable : (prefixWord ++ tailWord_4945708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945708).length < 2 ^ (prefixWord ++ tailWord_4945708).sum := by decide
  have hdescent : baseEnd_4945708 < baseStart_4945708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945715 : List Nat := [1, 1, 1, 2, 7, 2, 1, 2, 2, 4]
def baseStart_4945715 : Nat := 118140960795 + 4945715 * 2 ^ 59
def prefixEnd_4945715 : Nat := 4983230072969 + 3 ^ 40 * 4945715 * 2
def baseEnd_4945715 : Nat := 846509658383740867005859

theorem tailTrace_4945715 : CollatzResearch.WordTrace tailWord_4945715 prefixEnd_4945715 846509658383740867005859 := by
  unfold tailWord_4945715
  simp only [CollatzResearch.WordTrace]
  refine ⟨180385045277526690720222599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120256696851684460480148399 180385045277526690720222599)
  ·
    refine ⟨270577567916290036080333899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180385045277526690720222599 270577567916290036080333899)
    ·
      refine ⟨405866351874435054120500849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270577567916290036080333899 405866351874435054120500849)
      ·
        refine ⟨304399763905826290590375637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 405866351874435054120500849 304399763905826290590375637)
        ·
          refine ⟨7134369466542803685711929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 304399763905826290590375637 7134369466542803685711929)
          ·
            refine ⟨5350777099907102764283947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7134369466542803685711929 5350777099907102764283947)
            ·
              refine ⟨8026165649860654146425921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5350777099907102764283947 8026165649860654146425921)
              ·
                refine ⟨6019624237395490609819441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8026165649860654146425921 6019624237395490609819441)
                ·
                  refine ⟨4514718178046617957364581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6019624237395490609819441 4514718178046617957364581)
                  ·
                    refine ⟨846509658383740867005859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4514718178046617957364581 846509658383740867005859)
                    ·
                      rfl

theorem cell23_4945715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 4].length) (baseStart_4945715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945715 prefixEnd_4945715 := by exact prefixLift 4945715
  have htrace : WordTrace (prefixWord ++ tailWord_4945715) baseStart_4945715 baseEnd_4945715 := by
    simpa [prefixWord, tailWord_4945715, baseEnd_4945715] using wordTrace_append hprefix tailTrace_4945715
  have hstable : (prefixWord ++ tailWord_4945715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945715).length < 2 ^ (prefixWord ++ tailWord_4945715).sum := by decide
  have hdescent : baseEnd_4945715 < baseStart_4945715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945722 : List Nat := [3, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2]
def baseStart_4945722 : Nat := 118140960795 + 4945722 * 2 ^ 59
def prefixEnd_4945722 : Nat := 4983230072969 + 3 ^ 40 * 4945722 * 2
def baseEnd_4945722 : Nat := 2539532569515804073630045

theorem tailTrace_4945722 : CollatzResearch.WordTrace tailWord_4945722 prefixEnd_4945722 2539532569515804073630045 := by
  unfold tailWord_4945722
  simp only [CollatzResearch.WordTrace]
  refine ⟨45096325147125332728931855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120256867059000887277151613 45096325147125332728931855)
  ·
    refine ⟨67644487720687999093397783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45096325147125332728931855 67644487720687999093397783)
    ·
      refine ⟨101466731581031998640096675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67644487720687999093397783 101466731581031998640096675)
      ·
        refine ⟨152200097371547997960145013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101466731581031998640096675 152200097371547997960145013)
        ·
          refine ⟨14268759128582624808763595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152200097371547997960145013 14268759128582624808763595)
          ·
            refine ⟨21403138692873937213145393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14268759128582624808763595 21403138692873937213145393)
            ·
              refine ⟨16052354019655452909859045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21403138692873937213145393 16052354019655452909859045)
              ·
                refine ⟨3009816378685397420598571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16052354019655452909859045 3009816378685397420598571)
                ·
                  refine ⟨4514724568028096130897857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3009816378685397420598571 4514724568028096130897857)
                  ·
                    refine ⟨3386043426021072098173393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4514724568028096130897857 3386043426021072098173393)
                    ·
                      refine ⟨2539532569515804073630045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3386043426021072098173393 2539532569515804073630045)
                      ·
                        rfl

theorem cell23_4945722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2].length) (baseStart_4945722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945722 prefixEnd_4945722 := by exact prefixLift 4945722
  have htrace : WordTrace (prefixWord ++ tailWord_4945722) baseStart_4945722 baseEnd_4945722 := by
    simpa [prefixWord, tailWord_4945722, baseEnd_4945722] using wordTrace_append hprefix tailTrace_4945722
  have hstable : (prefixWord ++ tailWord_4945722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945722).length < 2 ^ (prefixWord ++ tailWord_4945722).sum := by decide
  have hdescent : baseEnd_4945722 < baseStart_4945722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945724 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 1, 9]
def baseStart_4945724 : Nat := 118140960795 + 4945724 * 2 ^ 59
def prefixEnd_4945724 : Nat := 4983230072969 + 3 ^ 40 * 4945724 * 2
def baseEnd_4945724 : Nat := 846511198825704355268345

theorem tailTrace_4945724 : CollatzResearch.WordTrace tailWord_4945724 prefixEnd_4945724 846511198825704355268345 := by
  unfold tailWord_4945724
  simp only [CollatzResearch.WordTrace]
  refine ⟨90192686767247042628650113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120256915689662723504866817 90192686767247042628650113)
  ·
    refine ⟨67644515075435281971487585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90192686767247042628650113 67644515075435281971487585)
    ·
      refine ⟨50733386306576461478615689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67644515075435281971487585 50733386306576461478615689)
      ·
        refine ⟨38050039729932346108961767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50733386306576461478615689 38050039729932346108961767)
        ·
          refine ⟨57075059594898519163442651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38050039729932346108961767 57075059594898519163442651)
          ·
            refine ⟨85612589392347778745163977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57075059594898519163442651 85612589392347778745163977)
            ·
              refine ⟨64209442044260834058872983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85612589392347778745163977 64209442044260834058872983)
              ·
                refine ⟨96314163066391251088309475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64209442044260834058872983 96314163066391251088309475)
                ·
                  refine ⟨144471244599586876632464213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96314163066391251088309475 144471244599586876632464213)
                  ·
                    refine ⟨846511198825704355268345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 144471244599586876632464213 846511198825704355268345)
                    ·
                      rfl

theorem cell23_4945724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_4945724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945724 prefixEnd_4945724 := by exact prefixLift 4945724
  have htrace : WordTrace (prefixWord ++ tailWord_4945724) baseStart_4945724 baseEnd_4945724 := by
    simpa [prefixWord, tailWord_4945724, baseEnd_4945724] using wordTrace_append hprefix tailTrace_4945724
  have hstable : (prefixWord ++ tailWord_4945724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945724).length < 2 ^ (prefixWord ++ tailWord_4945724).sum := by decide
  have hdescent : baseEnd_4945724 < baseStart_4945724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945756 : List Nat := [2, 2, 4, 2, 2, 2, 1, 3, 1, 2, 2]
def baseStart_4945756 : Nat := 118140960795 + 4945756 * 2 ^ 59
def prefixEnd_4945756 : Nat := 4983230072969 + 3 ^ 40 * 4945756 * 2
def baseEnd_4945756 : Nat := 2539550027858056940604889

theorem tailTrace_4945756 : CollatzResearch.WordTrace tailWord_4945756 prefixEnd_4945756 2539550027858056940604889 := by
  unfold tailWord_4945756
  simp only [CollatzResearch.WordTrace]
  refine ⟨90193270335189077361232561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120257693780252103148310081 90193270335189077361232561)
  ·
    refine ⟨67644952751391808020924421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90193270335189077361232561 67644952751391808020924421)
    ·
      refine ⟨12683428640885964003923329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67644952751391808020924421 12683428640885964003923329)
      ·
        refine ⟨9512571480664473002942497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12683428640885964003923329 9512571480664473002942497)
        ·
          refine ⟨7134428610498354752206873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9512571480664473002942497 7134428610498354752206873)
          ·
            refine ⟨5350821457873766064155155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7134428610498354752206873 5350821457873766064155155)
            ·
              refine ⟨8026232186810649096232733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5350821457873766064155155 8026232186810649096232733)
              ·
                refine ⟨3009837070053993411087275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8026232186810649096232733 3009837070053993411087275)
                ·
                  refine ⟨4514755605080990116630913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3009837070053993411087275 4514755605080990116630913)
                  ·
                    refine ⟨3386066703810742587473185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4514755605080990116630913 3386066703810742587473185)
                    ·
                      refine ⟨2539550027858056940604889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3386066703810742587473185 2539550027858056940604889)
                      ·
                        rfl

theorem cell23_4945756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_4945756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945756 prefixEnd_4945756 := by exact prefixLift 4945756
  have htrace : WordTrace (prefixWord ++ tailWord_4945756) baseStart_4945756 baseEnd_4945756 := by
    simpa [prefixWord, tailWord_4945756, baseEnd_4945756] using wordTrace_append hprefix tailTrace_4945756
  have hstable : (prefixWord ++ tailWord_4945756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945756).length < 2 ^ (prefixWord ++ tailWord_4945756).sum := by decide
  have hdescent : baseEnd_4945756 < baseStart_4945756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945781 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_4945781 : Nat := 118140960795 + 4945781 * 2 ^ 59
def prefixEnd_4945781 : Nat := 4983230072969 + 3 ^ 40 * 4945781 * 2
def baseEnd_4945781 : Nat := 2539562864874419342792273

theorem tailTrace_4945781 : CollatzResearch.WordTrace tailWord_4945781 prefixEnd_4945781 2539562864874419342792273 := by
  unfold tailWord_4945781
  simp only [CollatzResearch.WordTrace]
  refine ⟨180387452495287583992125197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120258301663525055994750131 180387452495287583992125197)
  ·
    refine ⟨67645294685732843997046949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180387452495287583992125197 67645294685732843997046949)
    ·
      refine ⟨12683492753574908249446303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67645294685732843997046949 12683492753574908249446303)
      ·
        refine ⟨19025239130362362374169455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12683492753574908249446303 19025239130362362374169455)
        ·
          refine ⟨28537858695543543561254183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19025239130362362374169455 28537858695543543561254183)
          ·
            refine ⟨42806788043315315341881275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28537858695543543561254183 42806788043315315341881275)
            ·
              refine ⟨64210182064972973012821913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42806788043315315341881275 64210182064972973012821913)
              ·
                refine ⟨48157636548729729759616435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64210182064972973012821913 48157636548729729759616435)
                ·
                  refine ⟨72236454823094594639424653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48157636548729729759616435 72236454823094594639424653)
                  ·
                    refine ⟨27088670558660472989784245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72236454823094594639424653 27088670558660472989784245)
                    ·
                      refine ⟨2539562864874419342792273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27088670558660472989784245 2539562864874419342792273)
                      ·
                        rfl

theorem cell23_4945781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_4945781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945781 prefixEnd_4945781 := by exact prefixLift 4945781
  have htrace : WordTrace (prefixWord ++ tailWord_4945781) baseStart_4945781 baseEnd_4945781 := by
    simpa [prefixWord, tailWord_4945781, baseEnd_4945781] using wordTrace_append hprefix tailTrace_4945781
  have hstable : (prefixWord ++ tailWord_4945781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945781).length < 2 ^ (prefixWord ++ tailWord_4945781).sum := by decide
  have hdescent : baseEnd_4945781 < baseStart_4945781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945799 : List Nat := [1, 1, 4, 2, 5, 1, 1, 2, 1, 3, 2]
def baseStart_4945799 : Nat := 118140960795 + 4945799 * 2 ^ 59
def prefixEnd_4945799 : Nat := 4983230072969 + 3 ^ 40 * 4945799 * 2
def baseEnd_4945799 : Nat := 2539572107526200272367191

theorem tailTrace_4945799 : CollatzResearch.WordTrace tailWord_4945799 prefixEnd_4945799 2539572107526200272367191 := by
  unfold tailWord_4945799
  simp only [CollatzResearch.WordTrace]
  refine ⟨180388109009222373066280451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120258739339481582044186967 180388109009222373066280451)
  ·
    refine ⟨270582163513833559599420677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180388109009222373066280451 270582163513833559599420677)
    ·
      refine ⟨50734155658843792424891377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 270582163513833559599420677 50734155658843792424891377)
      ·
        refine ⟨38050616744132844318668533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50734155658843792424891377 38050616744132844318668533)
        ·
          refine ⟨3567245319762454154875175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38050616744132844318668533 3567245319762454154875175)
          ·
            refine ⟨5350867979643681232312763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3567245319762454154875175 5350867979643681232312763)
            ·
              refine ⟨8026301969465521848469145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5350867979643681232312763 8026301969465521848469145)
              ·
                refine ⟨6019726477099141386351859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8026301969465521848469145 6019726477099141386351859)
                ·
                  refine ⟨9029589715648712079527789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6019726477099141386351859 9029589715648712079527789)
                  ·
                    refine ⟨3386096143368267029822921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9029589715648712079527789 3386096143368267029822921)
                    ·
                      refine ⟨2539572107526200272367191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3386096143368267029822921 2539572107526200272367191)
                      ·
                        rfl

theorem cell23_4945799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_4945799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945799 prefixEnd_4945799 := by exact prefixLift 4945799
  have htrace : WordTrace (prefixWord ++ tailWord_4945799) baseStart_4945799 baseEnd_4945799 := by
    simpa [prefixWord, tailWord_4945799, baseEnd_4945799] using wordTrace_append hprefix tailTrace_4945799
  have hstable : (prefixWord ++ tailWord_4945799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945799).length < 2 ^ (prefixWord ++ tailWord_4945799).sum := by decide
  have hdescent : baseEnd_4945799 < baseStart_4945799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945851 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 4]
def baseStart_4945851 : Nat := 118140960795 + 4945851 * 2 ^ 59
def prefixEnd_4945851 : Nat := 4983230072969 + 3 ^ 40 * 4945851 * 2
def baseEnd_4945851 : Nat := 2539598808520234068916951

theorem tailTrace_4945851 : CollatzResearch.WordTrace tailWord_4945851 prefixEnd_4945851 2539598808520234068916951 := by
  unfold tailWord_4945851
  simp only [CollatzResearch.WordTrace]
  refine ⟨180390005605033985947173407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120260003736689323964782271 180390005605033985947173407)
  ·
    refine ⟨270585008407550978920760111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180390005605033985947173407 270585008407550978920760111)
    ·
      refine ⟨405877512611326468381140167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270585008407550978920760111 405877512611326468381140167)
      ·
        refine ⟨608816268916989702571710251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405877512611326468381140167 608816268916989702571710251)
        ·
          refine ⟨913224403375484553857565377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608816268916989702571710251 913224403375484553857565377)
          ·
            refine ⟨684918302531613415393174033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 913224403375484553857565377 684918302531613415393174033)
            ·
              refine ⟨513688726898710061544880525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 684918302531613415393174033 513688726898710061544880525)
              ·
                refine ⟨192633272587016273079330197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 513688726898710061544880525 192633272587016273079330197)
                ·
                  refine ⟨9029684652516387800593603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 192633272587016273079330197 9029684652516387800593603)
                  ·
                    refine ⟨13544526978774581700890405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9029684652516387800593603 13544526978774581700890405)
                    ·
                      refine ⟨2539598808520234068916951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13544526978774581700890405 2539598808520234068916951)
                      ·
                        rfl

theorem cell23_4945851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 4].length) (baseStart_4945851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945851 prefixEnd_4945851 := by exact prefixLift 4945851
  have htrace : WordTrace (prefixWord ++ tailWord_4945851) baseStart_4945851 baseEnd_4945851 := by
    simpa [prefixWord, tailWord_4945851, baseEnd_4945851] using wordTrace_append hprefix tailTrace_4945851
  have hstable : (prefixWord ++ tailWord_4945851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945851).length < 2 ^ (prefixWord ++ tailWord_4945851).sum := by decide
  have hdescent : baseEnd_4945851 < baseStart_4945851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945868 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 1, 3, 4]
def baseStart_4945868 : Nat := 118140960795 + 4945868 * 2 ^ 59
def prefixEnd_4945868 : Nat := 4983230072969 + 3 ^ 40 * 4945868 * 2
def baseEnd_4945868 : Nat := 2539607537691360502404373

theorem tailTrace_4945868 : CollatzResearch.WordTrace tailWord_4945868 prefixEnd_4945868 2539607537691360502404373 := by
  unfold tailWord_4945868
  simp only [CollatzResearch.WordTrace]
  refine ⟨90195312822986198925271129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120260417097314931900361505 90195312822986198925271129)
  ·
    refine ⟨67646484617239649193953347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90195312822986198925271129 67646484617239649193953347)
    ·
      refine ⟨101469726925859473790930021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67646484617239649193953347 101469726925859473790930021)
      ·
        refine ⟨19025573798598651335799379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101469726925859473790930021 19025573798598651335799379)
        ·
          refine ⟨28538360697897977003699069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19025573798598651335799379 28538360697897977003699069)
          ·
            refine ⟨10701885261711741376387151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28538360697897977003699069 10701885261711741376387151)
            ·
              refine ⟨16052827892567612064580727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10701885261711741376387151 16052827892567612064580727)
              ·
                refine ⟨24079241838851418096871091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16052827892567612064580727 24079241838851418096871091)
                ·
                  refine ⟨36118862758277127145306637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24079241838851418096871091 36118862758277127145306637)
                  ·
                    refine ⟨13544573534353922679489989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36118862758277127145306637 13544573534353922679489989)
                    ·
                      refine ⟨2539607537691360502404373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13544573534353922679489989 2539607537691360502404373)
                      ·
                        rfl

theorem cell23_4945868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_4945868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945868 prefixEnd_4945868 := by exact prefixLift 4945868
  have htrace : WordTrace (prefixWord ++ tailWord_4945868) baseStart_4945868 baseEnd_4945868 := by
    simpa [prefixWord, tailWord_4945868, baseEnd_4945868] using wordTrace_append hprefix tailTrace_4945868
  have hstable : (prefixWord ++ tailWord_4945868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945868).length < 2 ^ (prefixWord ++ tailWord_4945868).sum := by decide
  have hdescent : baseEnd_4945868 < baseStart_4945868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945888 : List Nat := [2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 3]
def baseStart_4945888 : Nat := 118140960795 + 4945888 * 2 ^ 59
def prefixEnd_4945888 : Nat := 4983230072969 + 3 ^ 40 * 4945888 * 2
def baseEnd_4945888 : Nat := 2539617807304450424154281

theorem tailTrace_4945888 : CollatzResearch.WordTrace tailWord_4945888 prefixEnd_4945888 2539617807304450424154281 := by
  unfold tailWord_4945888
  simp only [CollatzResearch.WordTrace]
  refine ⟨90195677552949970633135159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120260903403933294177513545 90195677552949970633135159)
  ·
    refine ⟨135293516329424955949702739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90195677552949970633135159 135293516329424955949702739)
    ·
      refine ⟨202940274494137433924554109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135293516329424955949702739 202940274494137433924554109)
      ·
        refine ⟨76102602935301537721707791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202940274494137433924554109 76102602935301537721707791)
        ·
          refine ⟨114153904402952306582561687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76102602935301537721707791 114153904402952306582561687)
          ·
            refine ⟨171230856604428459873842531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114153904402952306582561687 171230856604428459873842531)
            ·
              refine ⟨256846284906642689810763797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171230856604428459873842531 256846284906642689810763797)
              ·
                refine ⟨12039669604998876084879553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 256846284906642689810763797 12039669604998876084879553)
                ·
                  refine ⟨9029752203749157063659665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12039669604998876084879553 9029752203749157063659665)
                  ·
                    refine ⟨6772314152811867797744749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9029752203749157063659665 6772314152811867797744749)
                    ·
                      refine ⟨2539617807304450424154281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6772314152811867797744749 2539617807304450424154281)
                      ·
                        rfl

theorem cell23_4945888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_4945888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945888 prefixEnd_4945888 := by exact prefixLift 4945888
  have htrace : WordTrace (prefixWord ++ tailWord_4945888) baseStart_4945888 baseEnd_4945888 := by
    simpa [prefixWord, tailWord_4945888, baseEnd_4945888] using wordTrace_append hprefix tailTrace_4945888
  have hstable : (prefixWord ++ tailWord_4945888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945888).length < 2 ^ (prefixWord ++ tailWord_4945888).sum := by decide
  have hdescent : baseEnd_4945888 < baseStart_4945888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945959 : List Nat := [1, 1, 7, 1, 2, 2, 2, 1, 6]
def baseStart_4945959 : Nat := 118140960795 + 4945959 * 2 ^ 59
def prefixEnd_4945959 : Nat := 4983230072969 + 3 ^ 40 * 4945959 * 2
def baseEnd_4945959 : Nat := 282183807158991071818495

theorem tailTrace_4945959 : CollatzResearch.WordTrace tailWord_4945959 prefixEnd_4945959 282183807158991071818495 := by
  unfold tailWord_4945959
  simp only [CollatzResearch.WordTrace]
  refine ⟨180393944688642720392104931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120262629792428480261403287 180393944688642720392104931)
  ·
    refine ⟨270590917032964080588157397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180393944688642720392104931 270590917032964080588157397)
    ·
      refine ⟨6341974617960095638784939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 270590917032964080588157397 6341974617960095638784939)
      ·
        refine ⟨9512961926940143458177409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6341974617960095638784939 9512961926940143458177409)
        ·
          refine ⟨7134721445205107593633057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9512961926940143458177409 7134721445205107593633057)
          ·
            refine ⟨5351041083903830695224793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7134721445205107593633057 5351041083903830695224793)
            ·
              refine ⟨4013280812927873021418595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5351041083903830695224793 4013280812927873021418595)
              ·
                refine ⟨6019921219391809532127893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4013280812927873021418595 6019921219391809532127893)
                ·
                  refine ⟨282183807158991071818495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6019921219391809532127893 282183807158991071818495)
                  ·
                    rfl

theorem cell23_4945959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 6].length) (baseStart_4945959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945959 prefixEnd_4945959 := by exact prefixLift 4945959
  have htrace : WordTrace (prefixWord ++ tailWord_4945959) baseStart_4945959 baseEnd_4945959 := by
    simpa [prefixWord, tailWord_4945959, baseEnd_4945959] using wordTrace_append hprefix tailTrace_4945959
  have hstable : (prefixWord ++ tailWord_4945959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945959).length < 2 ^ (prefixWord ++ tailWord_4945959).sum := by decide
  have hdescent : baseEnd_4945959 < baseStart_4945959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945961 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 4, 5, 5]
def baseStart_4945961 : Nat := 118140960795 + 4945961 * 2 ^ 59
def prefixEnd_4945961 : Nat := 4983230072969 + 3 ^ 40 * 4945961 * 2
def baseEnd_4945961 : Nat := 2539655291392228638541445

theorem tailTrace_4945961 : CollatzResearch.WordTrace tailWord_4945961 prefixEnd_4945961 2539655291392228638541445 := by
  unfold tailWord_4945961
  simp only [CollatzResearch.WordTrace]
  refine ⟨180394017634635474733677737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120262678423090316489118491 180394017634635474733677737)
  ·
    refine ⟨135295513225976606050258303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180394017634635474733677737 135295513225976606050258303)
    ·
      refine ⟨202943269838964909075387455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135295513225976606050258303 202943269838964909075387455)
      ·
        refine ⟨304414904758447363613081183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202943269838964909075387455 304414904758447363613081183)
        ·
          refine ⟨456622357137671045419621775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304414904758447363613081183 456622357137671045419621775)
          ·
            refine ⟨684933535706506568129432663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456622357137671045419621775 684933535706506568129432663)
            ·
              refine ⟨1027400303559759852194148995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684933535706506568129432663 1027400303559759852194148995)
              ·
                refine ⟨1541100455339639778291223493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1027400303559759852194148995 1541100455339639778291223493)
                ·
                  refine ⟨288956335376182458429604405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1541100455339639778291223493 288956335376182458429604405)
                  ·
                    refine ⟨27089656441517105477775413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 288956335376182458429604405 27089656441517105477775413)
                    ·
                      refine ⟨2539655291392228638541445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27089656441517105477775413 2539655291392228638541445)
                      ·
                        rfl

theorem cell23_4945961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_4945961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945961 prefixEnd_4945961 := by exact prefixLift 4945961
  have htrace : WordTrace (prefixWord ++ tailWord_4945961) baseStart_4945961 baseEnd_4945961 := by
    simpa [prefixWord, tailWord_4945961, baseEnd_4945961] using wordTrace_append hprefix tailTrace_4945961
  have hstable : (prefixWord ++ tailWord_4945961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945961).length < 2 ^ (prefixWord ++ tailWord_4945961).sum := by decide
  have hdescent : baseEnd_4945961 < baseStart_4945961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945972 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_4945972 : Nat := 118140960795 + 4945972 * 2 ^ 59
def prefixEnd_4945972 : Nat := 4983230072969 + 3 ^ 40 * 4945972 * 2
def baseEnd_4945972 : Nat := 846553646559809365167965

theorem tailTrace_4945972 : CollatzResearch.WordTrace tailWord_4945972 prefixEnd_4945972 846553646559809365167965 := by
  unfold tailWord_4945972
  simp only [CollatzResearch.WordTrace]
  refine ⟨90197209418797811806164085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120262945891730415741552113 90197209418797811806164085)
  ·
    refine ⟨8455988383012294856827883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90197209418797811806164085 8455988383012294856827883)
    ·
      refine ⟨12683982574518442285241825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8455988383012294856827883 12683982574518442285241825)
      ·
        refine ⟨9512986930888831713931369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12683982574518442285241825 9512986930888831713931369)
        ·
          refine ⟨7134740198166623785448527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9512986930888831713931369 7134740198166623785448527)
          ·
            refine ⟨10702110297249935678172791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7134740198166623785448527 10702110297249935678172791)
            ·
              refine ⟨16053165445874903517259187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10702110297249935678172791 16053165445874903517259187)
              ·
                refine ⟨24079748168812355275888781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16053165445874903517259187 24079748168812355275888781)
                ·
                  refine ⟨9029905563304633228458293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24079748168812355275888781 9029905563304633228458293)
                  ·
                    refine ⟨846553646559809365167965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9029905563304633228458293 846553646559809365167965)
                    ·
                      rfl

theorem cell23_4945972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_4945972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945972 prefixEnd_4945972 := by exact prefixLift 4945972
  have htrace : WordTrace (prefixWord ++ tailWord_4945972) baseStart_4945972 baseEnd_4945972 := by
    simpa [prefixWord, tailWord_4945972, baseEnd_4945972] using wordTrace_append hprefix tailTrace_4945972
  have hstable : (prefixWord ++ tailWord_4945972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945972).length < 2 ^ (prefixWord ++ tailWord_4945972).sum := by decide
  have hdescent : baseEnd_4945972 < baseStart_4945972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945975 : List Nat := [1, 1, 3, 1, 2, 2, 5, 2, 1, 1, 4]
def baseStart_4945975 : Nat := 118140960795 + 4945975 * 2 ^ 59
def prefixEnd_4945975 : Nat := 4983230072969 + 3 ^ 40 * 4945975 * 2
def baseEnd_4945975 : Nat := 2539662480121391583766381

theorem tailTrace_4945975 : CollatzResearch.WordTrace tailWord_4945975 prefixEnd_4945975 2539662480121391583766381 := by
  unfold tailWord_4945975
  simp only [CollatzResearch.WordTrace]
  refine ⟨180394528256584755124687379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120263018837723170083124919 180394528256584755124687379)
  ·
    refine ⟨270591792384877132687031069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180394528256584755124687379 270591792384877132687031069)
    ·
      refine ⟨101471922144328924757636651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270591792384877132687031069 101471922144328924757636651)
      ·
        refine ⟨152207883216493387136454977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101471922144328924757636651 152207883216493387136454977)
        ·
          refine ⟨114155912412370040352341233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152207883216493387136454977 114155912412370040352341233)
          ·
            refine ⟨85616934309277530264255925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114155912412370040352341233 85616934309277530264255925)
            ·
              refine ⟨8026587591494768462273993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85616934309277530264255925 8026587591494768462273993)
              ·
                refine ⟨6019940693621076346705495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8026587591494768462273993 6019940693621076346705495)
                ·
                  refine ⟨9029911040431614520058243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6019940693621076346705495 9029911040431614520058243)
                  ·
                    refine ⟨13544866560647421780087365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9029911040431614520058243 13544866560647421780087365)
                    ·
                      refine ⟨2539662480121391583766381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13544866560647421780087365 2539662480121391583766381)
                      ·
                        rfl

theorem cell23_4945975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 1, 4].length) (baseStart_4945975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945975 prefixEnd_4945975 := by exact prefixLift 4945975
  have htrace : WordTrace (prefixWord ++ tailWord_4945975) baseStart_4945975 baseEnd_4945975 := by
    simpa [prefixWord, tailWord_4945975, baseEnd_4945975] using wordTrace_append hprefix tailTrace_4945975
  have hstable : (prefixWord ++ tailWord_4945975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945975).length < 2 ^ (prefixWord ++ tailWord_4945975).sum := by decide
  have hdescent : baseEnd_4945975 < baseStart_4945975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945985 : List Nat := [1, 2, 5, 1, 2, 2, 1, 2, 1, 6]
def baseStart_4945985 : Nat := 118140960795 + 4945985 * 2 ^ 59
def prefixEnd_4945985 : Nat := 4983230072969 + 3 ^ 40 * 4945985 * 2
def baseEnd_4945985 : Nat := 846555871642645514880445

theorem tailTrace_4945985 : CollatzResearch.WordTrace tailWord_4945985 prefixEnd_4945985 846555871642645514880445 := by
  unfold tailWord_4945985
  simp only [CollatzResearch.WordTrace]
  refine ⟨180394892986548526832551409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120263261991032351221700939 180394892986548526832551409)
  ·
    refine ⟨135296169739911395124413557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180394892986548526832551409 135296169739911395124413557)
    ·
      refine ⟨12684015913116693292913771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135296169739911395124413557 12684015913116693292913771)
      ·
        refine ⟨19026023869675039939370657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12684015913116693292913771 19026023869675039939370657)
        ·
          refine ⟨14269517902256279954527993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19026023869675039939370657 14269517902256279954527993)
          ·
            refine ⟨10702138426692209965895995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14269517902256279954527993 10702138426692209965895995)
            ·
              refine ⟨16053207640038314948843993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10702138426692209965895995 16053207640038314948843993)
              ·
                refine ⟨12039905730028736211632995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16053207640038314948843993 12039905730028736211632995)
                ·
                  refine ⟨18059858595043104317449493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12039905730028736211632995 18059858595043104317449493)
                  ·
                    refine ⟨846555871642645514880445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18059858595043104317449493 846555871642645514880445)
                    ·
                      rfl

theorem cell23_4945985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_4945985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4945985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4945985 prefixEnd_4945985 := by exact prefixLift 4945985
  have htrace : WordTrace (prefixWord ++ tailWord_4945985) baseStart_4945985 baseEnd_4945985 := by
    simpa [prefixWord, tailWord_4945985, baseEnd_4945985] using wordTrace_append hprefix tailTrace_4945985
  have hstable : (prefixWord ++ tailWord_4945985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945985).length < 2 ^ (prefixWord ++ tailWord_4945985).sum := by decide
  have hdescent : baseEnd_4945985 < baseStart_4945985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946009 : List Nat := [1, 2, 1, 2, 2, 1, 5, 4, 1, 2, 2]
def baseStart_4946009 : Nat := 118140960795 + 4946009 * 2 ^ 59
def prefixEnd_4946009 : Nat := 4983230072969 + 3 ^ 40 * 4946009 * 2
def baseEnd_4946009 : Nat := 2539679938463644450741225

theorem tailTrace_4946009 : CollatzResearch.WordTrace tailWord_4946009 prefixEnd_4946009 2539679938463644450741225 := by
  unfold tailWord_4946009
  simp only [CollatzResearch.WordTrace]
  refine ⟨180395768338461578931425081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120263845558974385954283387 180395768338461578931425081)
  ·
    refine ⟨135296826253846184198568811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180395768338461578931425081 135296826253846184198568811)
    ·
      refine ⟨202945239380769276297853217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135296826253846184198568811 202945239380769276297853217)
      ·
        refine ⟨152208929535576957223389913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202945239380769276297853217 152208929535576957223389913)
        ·
          refine ⟨114156697151682717917542435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152208929535576957223389913 114156697151682717917542435)
          ·
            refine ⟨171235045727524076876313653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114156697151682717917542435 171235045727524076876313653)
            ·
              refine ⟨16053285536955382207154405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 171235045727524076876313653 16053285536955382207154405)
              ·
                refine ⟨3009991038179134163841451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16053285536955382207154405 3009991038179134163841451)
                ·
                  refine ⟨4514986557268701245762177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3009991038179134163841451 4514986557268701245762177)
                  ·
                    refine ⟨3386239917951525934321633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4514986557268701245762177 3386239917951525934321633)
                    ·
                      refine ⟨2539679938463644450741225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3386239917951525934321633 2539679938463644450741225)
                      ·
                        rfl

theorem cell23_4946009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 1, 2, 2].length) (baseStart_4946009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946009 prefixEnd_4946009 := by exact prefixLift 4946009
  have htrace : WordTrace (prefixWord ++ tailWord_4946009) baseStart_4946009 baseEnd_4946009 := by
    simpa [prefixWord, tailWord_4946009, baseEnd_4946009] using wordTrace_append hprefix tailTrace_4946009
  have hstable : (prefixWord ++ tailWord_4946009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946009).length < 2 ^ (prefixWord ++ tailWord_4946009).sum := by decide
  have hdescent : baseEnd_4946009 < baseStart_4946009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946025 : List Nat := [1, 2, 1, 1, 1, 5, 4, 1, 1, 3, 3]
def baseStart_4946025 : Nat := 118140960795 + 4946025 * 2 ^ 59
def prefixEnd_4946025 : Nat := 4983230072969 + 3 ^ 40 * 4946025 * 2
def baseEnd_4946025 : Nat := 2539688154154116388141151

theorem tailTrace_4946025 : CollatzResearch.WordTrace tailWord_4946025 prefixEnd_4946025 2539688154154116388141151 := by
  unfold tailWord_4946025
  simp only [CollatzResearch.WordTrace]
  refine ⟨180396351906403613664007529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120264234604269075776005019 180396351906403613664007529)
  ·
    refine ⟨135297263929802710248005647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180396351906403613664007529 135297263929802710248005647)
    ·
      refine ⟨202945895894704065372008471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135297263929802710248005647 202945895894704065372008471)
      ·
        refine ⟨304418843842056098058012707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202945895894704065372008471 304418843842056098058012707)
        ·
          refine ⟨456628265763084147087019061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304418843842056098058012707 456628265763084147087019061)
          ·
            refine ⟨42808899915289138789408037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 456628265763084147087019061 42808899915289138789408037)
            ·
              refine ⟨8026668734116713523014007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42808899915289138789408037 8026668734116713523014007)
              ·
                refine ⟨12040003101175070284521011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8026668734116713523014007 12040003101175070284521011)
                ·
                  refine ⟨18060004651762605426781517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12040003101175070284521011 18060004651762605426781517)
                  ·
                    refine ⟨6772501744410977035043069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18060004651762605426781517 6772501744410977035043069)
                    ·
                      refine ⟨2539688154154116388141151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6772501744410977035043069 2539688154154116388141151)
                      ·
                        rfl

theorem cell23_4946025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 3, 3].length) (baseStart_4946025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946025 prefixEnd_4946025 := by exact prefixLift 4946025
  have htrace : WordTrace (prefixWord ++ tailWord_4946025) baseStart_4946025 baseEnd_4946025 := by
    simpa [prefixWord, tailWord_4946025, baseEnd_4946025] using wordTrace_append hprefix tailTrace_4946025
  have hstable : (prefixWord ++ tailWord_4946025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946025).length < 2 ^ (prefixWord ++ tailWord_4946025).sum := by decide
  have hdescent : baseEnd_4946025 < baseStart_4946025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946070 : List Nat := [5, 3, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_4946070 : Nat := 118140960795 + 4946070 * 2 ^ 59
def prefixEnd_4946070 : Nat := 4983230072969 + 3 ^ 40 * 4946070 * 2
def baseEnd_4946070 : Nat := 846570420261189570692815

theorem tailTrace_4946070 : CollatzResearch.WordTrace tailWord_4946070 prefixEnd_4946070 846570420261189570692815 := by
  unfold tailWord_4946070
  simp only [CollatzResearch.WordTrace]
  refine ⟨11274874574452536646837229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120265328794160390899597109 11274874574452536646837229)
  ·
    refine ⟨4228077965419701242563961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11274874574452536646837229 4228077965419701242563961)
    ·
      refine ⟨3171058474064775931922971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4228077965419701242563961 3171058474064775931922971)
      ·
        refine ⟨4756587711097163897884457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3171058474064775931922971 4756587711097163897884457)
        ·
          refine ⟨3567440783322872923413343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4756587711097163897884457 3567440783322872923413343)
          ·
            refine ⟨5351161174984309385120015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3567440783322872923413343 5351161174984309385120015)
            ·
              refine ⟨8026741762476464077680023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5351161174984309385120015 8026741762476464077680023)
              ·
                refine ⟨12040112643714696116520035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8026741762476464077680023 12040112643714696116520035)
                ·
                  refine ⟨18060168965572044174780053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12040112643714696116520035 18060168965572044174780053)
                  ·
                    refine ⟨846570420261189570692815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18060168965572044174780053 846570420261189570692815)
                    ·
                      rfl

theorem cell23_4946070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_4946070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946070 prefixEnd_4946070 := by exact prefixLift 4946070
  have htrace : WordTrace (prefixWord ++ tailWord_4946070) baseStart_4946070 baseEnd_4946070 := by
    simpa [prefixWord, tailWord_4946070, baseEnd_4946070] using wordTrace_append hprefix tailTrace_4946070
  have hstable : (prefixWord ++ tailWord_4946070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946070).length < 2 ^ (prefixWord ++ tailWord_4946070).sum := by decide
  have hdescent : baseEnd_4946070 < baseStart_4946070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946152 : List Nat := [2, 1, 4, 1, 2, 3, 2, 1, 2, 5]
def baseStart_4946152 : Nat := 118140960795 + 4946152 * 2 ^ 59
def prefixEnd_4946152 : Nat := 4983230072969 + 3 ^ 40 * 4946152 * 2
def baseEnd_4946152 : Nat := 846584455399079130417689

theorem tailTrace_4946152 : CollatzResearch.WordTrace tailWord_4946152 prefixEnd_4946152 846584455399079130417689 := by
  unfold tailWord_4946152
  simp only [CollatzResearch.WordTrace]
  refine ⟨90200491988471757176940355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120267322651295676235920473 90200491988471757176940355)
  ·
    refine ⟨135300737982707635765410533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90200491988471757176940355 135300737982707635765410533)
    ·
      refine ⟨25368888371757681706014475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135300737982707635765410533 25368888371757681706014475)
      ·
        refine ⟨38053332557636522559021713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25368888371757681706014475 38053332557636522559021713)
        ·
          refine ⟨28539999418227391919266285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38053332557636522559021713 28539999418227391919266285)
          ·
            refine ⟨10702499781835271969724857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28539999418227391919266285 10702499781835271969724857)
            ·
              refine ⟨8026874836376453977293643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10702499781835271969724857 8026874836376453977293643)
              ·
                refine ⟨12040312254564680965940465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8026874836376453977293643 12040312254564680965940465)
                ·
                  refine ⟨9030234190923510724455349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12040312254564680965940465 9030234190923510724455349)
                  ·
                    refine ⟨846584455399079130417689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9030234190923510724455349 846584455399079130417689)
                    ·
                      rfl

theorem cell23_4946152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_4946152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946152 prefixEnd_4946152 := by exact prefixLift 4946152
  have htrace : WordTrace (prefixWord ++ tailWord_4946152) baseStart_4946152 baseEnd_4946152 := by
    simpa [prefixWord, tailWord_4946152, baseEnd_4946152] using wordTrace_append hprefix tailTrace_4946152
  have hstable : (prefixWord ++ tailWord_4946152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946152).length < 2 ^ (prefixWord ++ tailWord_4946152).sum := by decide
  have hdescent : baseEnd_4946152 < baseStart_4946152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946172 : List Nat := [2, 2, 2, 1, 4, 1, 2, 2, 2, 1, 4]
def baseStart_4946172 : Nat := 118140960795 + 4946172 * 2 ^ 59
def prefixEnd_4946172 : Nat := 4983230072969 + 3 ^ 40 * 4946172 * 2
def baseEnd_4946172 : Nat := 2539763635810327313002975

theorem tailTrace_4946172 : CollatzResearch.WordTrace tailWord_4946172 prefixEnd_4946172 2539763635810327313002975 := by
  unfold tailWord_4946172
  simp only [CollatzResearch.WordTrace]
  refine ⟨90200856718435528884804385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120267808957914038513072513 90200856718435528884804385)
  ·
    refine ⟨67650642538826646663603289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90200856718435528884804385 67650642538826646663603289)
    ·
      refine ⟨50737981904119984997702467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67650642538826646663603289 50737981904119984997702467)
      ·
        refine ⟨76106972856179977496553701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50737981904119984997702467 76106972856179977496553701)
        ·
          refine ⟨14270057410533745780603819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76106972856179977496553701 14270057410533745780603819)
          ·
            refine ⟨21405086115800618670905729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14270057410533745780603819 21405086115800618670905729)
            ·
              refine ⟨16053814586850464003179297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21405086115800618670905729 16053814586850464003179297)
              ·
                refine ⟨12040360940137848002384473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16053814586850464003179297 12040360940137848002384473)
                ·
                  refine ⟨9030270705103386001788355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12040360940137848002384473 9030270705103386001788355)
                  ·
                    refine ⟨13545406057655079002682533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9030270705103386001788355 13545406057655079002682533)
                    ·
                      refine ⟨2539763635810327313002975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13545406057655079002682533 2539763635810327313002975)
                      ·
                        rfl

theorem cell23_4946172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_4946172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946172 prefixEnd_4946172 := by exact prefixLift 4946172
  have htrace : WordTrace (prefixWord ++ tailWord_4946172) baseStart_4946172 baseEnd_4946172 := by
    simpa [prefixWord, tailWord_4946172, baseEnd_4946172] using wordTrace_append hprefix tailTrace_4946172
  have hstable : (prefixWord ++ tailWord_4946172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946172).length < 2 ^ (prefixWord ++ tailWord_4946172).sum := by decide
  have hdescent : baseEnd_4946172 < baseStart_4946172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946206 : List Nat := [4, 3, 2, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_4946206 : Nat := 118140960795 + 4946206 * 2 ^ 59
def prefixEnd_4946206 : Nat := 4983230072969 + 3 ^ 40 * 4946206 * 2
def baseEnd_4946206 : Nat := 2539781094152580179977819

theorem tailTrace_4946206 : CollatzResearch.WordTrace tailWord_4946206 prefixEnd_4946206 2539781094152580179977819 := by
  unfold tailWord_4946206
  simp only [CollatzResearch.WordTrace]
  refine ⟨22550369189843485197043309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120268635679165254384230981 22550369189843485197043309)
  ·
    refine ⟨8456388446191306948891241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22550369189843485197043309 8456388446191306948891241)
    ·
      refine ⟨6342291334643480211668431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8456388446191306948891241 6342291334643480211668431)
      ·
        refine ⟨9513437001965220317502647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6342291334643480211668431 9513437001965220317502647)
        ·
          refine ⟨14270155502947830476253971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9513437001965220317502647 14270155502947830476253971)
          ·
            refine ⟨21405233254421745714380957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14270155502947830476253971 21405233254421745714380957)
            ·
              refine ⟨8026962470408154642892859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21405233254421745714380957 8026962470408154642892859)
              ·
                refine ⟨12040443705612231964339289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8026962470408154642892859 12040443705612231964339289)
                ·
                  refine ⟨9030332779209173973254467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12040443705612231964339289 9030332779209173973254467)
                  ·
                    refine ⟨13545499168813760959881701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9030332779209173973254467 13545499168813760959881701)
                    ·
                      refine ⟨2539781094152580179977819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13545499168813760959881701 2539781094152580179977819)
                      ·
                        rfl

theorem cell23_4946206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_4946206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946206 prefixEnd_4946206 := by exact prefixLift 4946206
  have htrace : WordTrace (prefixWord ++ tailWord_4946206) baseStart_4946206 baseEnd_4946206 := by
    simpa [prefixWord, tailWord_4946206, baseEnd_4946206] using wordTrace_append hprefix tailTrace_4946206
  have hstable : (prefixWord ++ tailWord_4946206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946206).length < 2 ^ (prefixWord ++ tailWord_4946206).sum := by decide
  have hdescent : baseEnd_4946206 < baseStart_4946206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946239 : List Nat := [1, 1, 2, 2, 4, 1, 4, 1, 3, 1, 3]
def baseStart_4946239 : Nat := 118140960795 + 4946239 * 2 ^ 59
def prefixEnd_4946239 : Nat := 4983230072969 + 3 ^ 40 * 4946239 * 2
def baseEnd_4946239 : Nat := 2539798039014178550865167

theorem tailTrace_4946239 : CollatzResearch.WordTrace tailWord_4946239 prefixEnd_4946239 2539798039014178550865167 := by
  unfold tailWord_4946239
  simp only [CollatzResearch.WordTrace]
  refine ⟨180404157127628328212297771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120269438085085552141531847 180404157127628328212297771)
  ·
    refine ⟨270606235691442492318446657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180404157127628328212297771 270606235691442492318446657)
    ·
      refine ⟨202954676768581869238834993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270606235691442492318446657 202954676768581869238834993)
      ·
        refine ⟨152216007576436401929126245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202954676768581869238834993 152216007576436401929126245)
        ·
          refine ⟨28540501420581825361711171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152216007576436401929126245 28540501420581825361711171)
          ·
            refine ⟨42810752130872738042566757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28540501420581825361711171 42810752130872738042566757)
            ·
              refine ⟨8027016024538638382981267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42810752130872738042566757 8027016024538638382981267)
              ·
                refine ⟨12040524036807957574471901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8027016024538638382981267 12040524036807957574471901)
                ·
                  refine ⟨4515196513802984090426963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12040524036807957574471901 4515196513802984090426963)
                  ·
                    refine ⟨6772794770704476135640445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4515196513802984090426963 6772794770704476135640445)
                    ·
                      refine ⟨2539798039014178550865167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6772794770704476135640445 2539798039014178550865167)
                      ·
                        rfl

theorem cell23_4946239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 1, 3].length) (baseStart_4946239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946239 prefixEnd_4946239 := by exact prefixLift 4946239
  have htrace : WordTrace (prefixWord ++ tailWord_4946239) baseStart_4946239 baseEnd_4946239 := by
    simpa [prefixWord, tailWord_4946239, baseEnd_4946239] using wordTrace_append hprefix tailTrace_4946239
  have hstable : (prefixWord ++ tailWord_4946239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946239).length < 2 ^ (prefixWord ++ tailWord_4946239).sum := by decide
  have hdescent : baseEnd_4946239 < baseStart_4946239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946255 : List Nat := [1, 1, 2, 1, 1, 2, 1, 7, 1, 6]
def baseStart_4946255 : Nat := 118140960795 + 4946255 * 2 ^ 59
def prefixEnd_4946255 : Nat := 4983230072969 + 3 ^ 40 * 4946255 * 2
def baseEnd_4946255 : Nat := 846602084901550162755031

theorem tailTrace_4946255 : CollatzResearch.WordTrace tailWord_4946255 prefixEnd_4946255 846602084901550162755031 := by
  unfold tailWord_4946255
  simp only [CollatzResearch.WordTrace]
  refine ⟨180404740695570362944880219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120269827130380241963253479 180404740695570362944880219)
  ·
    refine ⟨270607111043355544417320329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180404740695570362944880219 270607111043355544417320329)
    ·
      refine ⟨202955333282516658312990247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270607111043355544417320329 202955333282516658312990247)
      ·
        refine ⟨304432999923774987469485371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202955333282516658312990247 304432999923774987469485371)
        ·
          refine ⟨456649499885662481204228057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304432999923774987469485371 456649499885662481204228057)
          ·
            refine ⟨342487124914246860903171043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 456649499885662481204228057 342487124914246860903171043)
            ·
              refine ⟨513730687371370291354756565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342487124914246860903171043 513730687371370291354756565)
              ·
                refine ⟨12040562985266491203627107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 513730687371370291354756565 12040562985266491203627107)
                ·
                  refine ⟨18060844477899736805440661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12040562985266491203627107 18060844477899736805440661)
                  ·
                    refine ⟨846602084901550162755031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18060844477899736805440661 846602084901550162755031)
                    ·
                      rfl

theorem cell23_4946255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 6].length) (baseStart_4946255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946255 prefixEnd_4946255 := by exact prefixLift 4946255
  have htrace : WordTrace (prefixWord ++ tailWord_4946255) baseStart_4946255 baseEnd_4946255 := by
    simpa [prefixWord, tailWord_4946255, baseEnd_4946255] using wordTrace_append hprefix tailTrace_4946255
  have hstable : (prefixWord ++ tailWord_4946255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946255).length < 2 ^ (prefixWord ++ tailWord_4946255).sum := by decide
  have hdescent : baseEnd_4946255 < baseStart_4946255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946265 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 5, 1, 5]
def baseStart_4946265 : Nat := 118140960795 + 4946265 * 2 ^ 59
def prefixEnd_4946265 : Nat := 4983230072969 + 3 ^ 40 * 4946265 * 2
def baseEnd_4946265 : Nat := 2539811389511195449140047

theorem tailTrace_4946265 : CollatzResearch.WordTrace tailWord_4946265 prefixEnd_4946265 2539811389511195449140047 := by
  unfold tailWord_4946265
  simp only [CollatzResearch.WordTrace]
  refine ⟨180405105425534134652744249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120270070283689423101829499 180405105425534134652744249)
  ·
    refine ⟨135303829069150600989558187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180405105425534134652744249 135303829069150600989558187)
    ·
      refine ⟨202955743603725901484337281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135303829069150600989558187 202955743603725901484337281)
      ·
        refine ⟨152216807702794426113252961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202955743603725901484337281 152216807702794426113252961)
        ·
          refine ⟨114162605777095819584939721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152216807702794426113252961 114162605777095819584939721)
          ·
            refine ⟨85621954332821864688704791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114162605777095819584939721 85621954332821864688704791)
            ·
              refine ⟨128432931499232797033057187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85621954332821864688704791 128432931499232797033057187)
              ·
                refine ⟨192649397248849195549585781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128432931499232797033057187 192649397248849195549585781)
                ·
                  refine ⟨18060880992079612082773667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 192649397248849195549585781 18060880992079612082773667)
                  ·
                    refine ⟨27091321488119418124160501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18060880992079612082773667 27091321488119418124160501)
                    ·
                      refine ⟨2539811389511195449140047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27091321488119418124160501 2539811389511195449140047)
                      ·
                        rfl

theorem cell23_4946265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_4946265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946265 prefixEnd_4946265 := by exact prefixLift 4946265
  have htrace : WordTrace (prefixWord ++ tailWord_4946265) baseStart_4946265 baseEnd_4946265 := by
    simpa [prefixWord, tailWord_4946265, baseEnd_4946265] using wordTrace_append hprefix tailTrace_4946265
  have hstable : (prefixWord ++ tailWord_4946265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946265).length < 2 ^ (prefixWord ++ tailWord_4946265).sum := by decide
  have hdescent : baseEnd_4946265 < baseStart_4946265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946279 : List Nat := [1, 1, 5, 1, 3, 1, 2, 3, 1, 1, 4]
def baseStart_4946279 : Nat := 118140960795 + 4946279 * 2 ^ 59
def prefixEnd_4946279 : Nat := 4983230072969 + 3 ^ 40 * 4946279 * 2
def baseEnd_4946279 : Nat := 2539818578240358394364983

theorem tailTrace_4946279 : CollatzResearch.WordTrace tailWord_4946279 prefixEnd_4946279 2539818578240358394364983 := by
  unfold tailWord_4946279
  simp only [CollatzResearch.WordTrace]
  refine ⟨180405616047483415043753891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120270410698322276695835927 180405616047483415043753891)
  ·
    refine ⟨270608424071225122565630837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180405616047483415043753891 270608424071225122565630837)
    ·
      refine ⟨25369539756677355240527891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 270608424071225122565630837 25369539756677355240527891)
      ·
        refine ⟨38054309635016032860791837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25369539756677355240527891 38054309635016032860791837)
        ·
          refine ⟨14270366113131012322796939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38054309635016032860791837 14270366113131012322796939)
          ·
            refine ⟨21405549169696518484195409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14270366113131012322796939 21405549169696518484195409)
            ·
              refine ⟨16054161877272388863146557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21405549169696518484195409 16054161877272388863146557)
              ·
                refine ⟨6020310703977145823679959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16054161877272388863146557 6020310703977145823679959)
                ·
                  refine ⟨9030466055965718735519939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6020310703977145823679959 9030466055965718735519939)
                  ·
                    refine ⟨13545699083948578103279909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9030466055965718735519939 13545699083948578103279909)
                    ·
                      refine ⟨2539818578240358394364983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13545699083948578103279909 2539818578240358394364983)
                      ·
                        rfl

theorem cell23_4946279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_4946279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946279 prefixEnd_4946279 := by exact prefixLift 4946279
  have htrace : WordTrace (prefixWord ++ tailWord_4946279) baseStart_4946279 baseEnd_4946279 := by
    simpa [prefixWord, tailWord_4946279, baseEnd_4946279] using wordTrace_append hprefix tailTrace_4946279
  have hstable : (prefixWord ++ tailWord_4946279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946279).length < 2 ^ (prefixWord ++ tailWord_4946279).sum := by decide
  have hdescent : baseEnd_4946279 < baseStart_4946279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946316 : List Nat := [2, 2, 1, 2, 1, 6, 1, 2, 1, 2, 3]
def baseStart_4946316 : Nat := 118140960795 + 4946316 * 2 ^ 59
def prefixEnd_4946316 : Nat := 4983230072969 + 3 ^ 40 * 4946316 * 2
def baseEnd_4946316 : Nat := 2539837577024574749602313

theorem tailTrace_4946316 : CollatzResearch.WordTrace tailWord_4946316 prefixEnd_4946316 2539837577024574749602313 := by
  unfold tailWord_4946316
  simp only [CollatzResearch.WordTrace]
  refine ⟨90203482774174685181425401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120271310365566246908567201 90203482774174685181425401)
  ·
    refine ⟨67652612080631013886069051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90203482774174685181425401 67652612080631013886069051)
    ·
      refine ⟨101478918120946520829103577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67652612080631013886069051 101478918120946520829103577)
      ·
        refine ⟨76109188590709890621827683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101478918120946520829103577 76109188590709890621827683)
        ·
          refine ⟨114163782886064835932741525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76109188590709890621827683 114163782886064835932741525)
          ·
            refine ⟨5351427322784289184347259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 114163782886064835932741525 5351427322784289184347259)
            ·
              refine ⟨8027140984176433776520889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5351427322784289184347259 8027140984176433776520889)
              ·
                refine ⟨6020355738132325332390667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8027140984176433776520889 6020355738132325332390667)
                ·
                  refine ⟨9030533607198487998586001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6020355738132325332390667 9030533607198487998586001)
                  ·
                    refine ⟨6772900205398865998939501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9030533607198487998586001 6772900205398865998939501)
                    ·
                      refine ⟨2539837577024574749602313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6772900205398865998939501 2539837577024574749602313)
                      ·
                        rfl

theorem cell23_4946316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_4946316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946316 prefixEnd_4946316 := by exact prefixLift 4946316
  have htrace : WordTrace (prefixWord ++ tailWord_4946316) baseStart_4946316 baseEnd_4946316 := by
    simpa [prefixWord, tailWord_4946316, baseEnd_4946316] using wordTrace_append hprefix tailTrace_4946316
  have hstable : (prefixWord ++ tailWord_4946316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946316).length < 2 ^ (prefixWord ++ tailWord_4946316).sum := by decide
  have hdescent : baseEnd_4946316 < baseStart_4946316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946333 : List Nat := [1, 4, 2, 1, 4, 1, 3, 1, 1, 2, 3]
def baseStart_4946333 : Nat := 118140960795 + 4946333 * 2 ^ 59
def prefixEnd_4946333 : Nat := 4983230072969 + 3 ^ 40 * 4946333 * 2
def baseEnd_4946333 : Nat := 2539846306195701183089735

theorem tailTrace_4946333 : CollatzResearch.WordTrace tailWord_4946333 prefixEnd_4946333 2539846306195701183089735 := by
  unfold tailWord_4946333
  simp only [CollatzResearch.WordTrace]
  refine ⟨180407585589287782266219653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120271723726191854844146435 180407585589287782266219653)
  ·
    refine ⟨33826422297991459174916185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180407585589287782266219653 33826422297991459174916185)
    ·
      refine ⟨25369816723493594381187139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33826422297991459174916185 25369816723493594381187139)
      ·
        refine ⟨38054725085240391571780709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25369816723493594381187139 38054725085240391571780709)
        ·
          refine ⟨7135260953482573419708883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38054725085240391571780709 7135260953482573419708883)
          ·
            refine ⟨10702891430223860129563325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7135260953482573419708883 10702891430223860129563325)
            ·
              refine ⟨4013584286333947548586247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10702891430223860129563325 4013584286333947548586247)
              ·
                refine ⟨6020376429500921322879371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4013584286333947548586247 6020376429500921322879371)
                ·
                  refine ⟨9030564644251381984319057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6020376429500921322879371 9030564644251381984319057)
                  ·
                    refine ⟨6772923483188536488239293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9030564644251381984319057 6772923483188536488239293)
                    ·
                      refine ⟨2539846306195701183089735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6772923483188536488239293 2539846306195701183089735)
                      ·
                        rfl

theorem cell23_4946333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_4946333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946333 prefixEnd_4946333 := by exact prefixLift 4946333
  have htrace : WordTrace (prefixWord ++ tailWord_4946333) baseStart_4946333 baseEnd_4946333 := by
    simpa [prefixWord, tailWord_4946333, baseEnd_4946333] using wordTrace_append hprefix tailTrace_4946333
  have hstable : (prefixWord ++ tailWord_4946333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946333).length < 2 ^ (prefixWord ++ tailWord_4946333).sum := by decide
  have hdescent : baseEnd_4946333 < baseStart_4946333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946345 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 3, 8]
def baseStart_4946345 : Nat := 118140960795 + 4946345 * 2 ^ 59
def prefixEnd_4946345 : Nat := 4983230072969 + 3 ^ 40 * 4946345 * 2
def baseEnd_4946345 : Nat := 846617489321185045379893

theorem tailTrace_4946345 : CollatzResearch.WordTrace tailWord_4946345 prefixEnd_4946345 846617489321185045379893 := by
  unfold tailWord_4946345
  simp only [CollatzResearch.WordTrace]
  refine ⟨180408023265244308315656489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120272015510162872210437659 180408023265244308315656489)
  ·
    refine ⟨135306017448933231236742367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180408023265244308315656489 135306017448933231236742367)
    ·
      refine ⟨202959026173399846855113551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135306017448933231236742367 202959026173399846855113551)
      ·
        refine ⟨304438539260099770282670327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202959026173399846855113551 304438539260099770282670327)
        ·
          refine ⟨456657808890149655424005491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304438539260099770282670327 456657808890149655424005491)
          ·
            refine ⟨684986713335224483136008237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456657808890149655424005491 684986713335224483136008237)
            ·
              refine ⟨256870017500709181176003089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 684986713335224483136008237 256870017500709181176003089)
              ·
                refine ⟨192652513125531885882002317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256870017500709181176003089 192652513125531885882002317)
                ·
                  refine ⟨72244692422074457205750869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192652513125531885882002317 72244692422074457205750869)
                  ·
                    refine ⟨846617489321185045379893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72244692422074457205750869 846617489321185045379893)
                    ·
                      rfl

theorem cell23_4946345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 8].length) (baseStart_4946345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946345 prefixEnd_4946345 := by exact prefixLift 4946345
  have htrace : WordTrace (prefixWord ++ tailWord_4946345) baseStart_4946345 baseEnd_4946345 := by
    simpa [prefixWord, tailWord_4946345, baseEnd_4946345] using wordTrace_append hprefix tailTrace_4946345
  have hstable : (prefixWord ++ tailWord_4946345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946345).length < 2 ^ (prefixWord ++ tailWord_4946345).sum := by decide
  have hdescent : baseEnd_4946345 < baseStart_4946345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946382 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_4946382 : Nat := 118140960795 + 4946382 * 2 ^ 59
def prefixEnd_4946382 : Nat := 4983230072969 + 3 ^ 40 * 4946382 * 2
def baseEnd_4946382 : Nat := 2539871466747771491377009

theorem tailTrace_4946382 : CollatzResearch.WordTrace tailWord_4946382 prefixEnd_4946382 2539871466747771491377009 := by
  unfold tailWord_4946382
  simp only [CollatzResearch.WordTrace]
  refine ⟨22551171595763782954344175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120272915177406842423168933 22551171595763782954344175)
  ·
    refine ⟨33826757393645674431516263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22551171595763782954344175 33826757393645674431516263)
    ·
      refine ⟨50740136090468511647274395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33826757393645674431516263 50740136090468511647274395)
      ·
        refine ⟨76110204135702767470911593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50740136090468511647274395 76110204135702767470911593)
        ·
          refine ⟨57082653101777075603183695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76110204135702767470911593 57082653101777075603183695)
          ·
            refine ⟨85623979652665613404775543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57082653101777075603183695 85623979652665613404775543)
            ·
              refine ⟨128435969478998420107163315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85623979652665613404775543 128435969478998420107163315)
              ·
                refine ⟨192653954218497630160744973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128435969478998420107163315 192653954218497630160744973)
                ·
                  refine ⟨72245232831936611310279365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192653954218497630160744973 72245232831936611310279365)
                  ·
                    refine ⟨13545981155988114620677381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72245232831936611310279365 13545981155988114620677381)
                    ·
                      refine ⟨2539871466747771491377009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13545981155988114620677381 2539871466747771491377009)
                      ·
                        rfl

theorem cell23_4946382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_4946382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946382 prefixEnd_4946382 := by exact prefixLift 4946382
  have htrace : WordTrace (prefixWord ++ tailWord_4946382) baseStart_4946382 baseEnd_4946382 := by
    simpa [prefixWord, tailWord_4946382, baseEnd_4946382] using wordTrace_append hprefix tailTrace_4946382
  have hstable : (prefixWord ++ tailWord_4946382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946382).length < 2 ^ (prefixWord ++ tailWord_4946382).sum := by decide
  have hdescent : baseEnd_4946382 < baseStart_4946382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946403 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 4, 2, 2]
def baseStart_4946403 : Nat := 118140960795 + 4946403 * 2 ^ 59
def prefixEnd_4946403 : Nat := 4983230072969 + 3 ^ 40 * 4946403 * 2
def baseEnd_4946403 : Nat := 2539882249841515909214413

theorem tailTrace_4946403 : CollatzResearch.WordTrace tailWord_4946403 prefixEnd_4946403 2539882249841515909214413 := by
  unfold tailWord_4946403
  simp only [CollatzResearch.WordTrace]
  refine ⟨180410138699034184221267863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120273425799356122814178575 180410138699034184221267863)
  ·
    refine ⟨270615208048551276331901795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180410138699034184221267863 270615208048551276331901795)
    ·
      refine ⟨405922812072826914497852693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270615208048551276331901795 405922812072826914497852693)
      ·
        refine ⟨19027631815913761617086845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 405922812072826914497852693 19027631815913761617086845)
        ·
          refine ⟨7135361930967660606407567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19027631815913761617086845 7135361930967660606407567)
          ·
            refine ⟨10703042896451490909611351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7135361930967660606407567 10703042896451490909611351)
            ·
              refine ⟨16054564344677236364417027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10703042896451490909611351 16054564344677236364417027)
              ·
                refine ⟨24081846517015854546625541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16054564344677236364417027 24081846517015854546625541)
                ·
                  refine ⟨4515346221940472727492289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24081846517015854546625541 4515346221940472727492289)
                  ·
                    refine ⟨3386509666455354545619217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4515346221940472727492289 3386509666455354545619217)
                    ·
                      refine ⟨2539882249841515909214413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3386509666455354545619217 2539882249841515909214413)
                      ·
                        rfl

theorem cell23_4946403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_4946403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946403 prefixEnd_4946403 := by exact prefixLift 4946403
  have htrace : WordTrace (prefixWord ++ tailWord_4946403) baseStart_4946403 baseEnd_4946403 := by
    simpa [prefixWord, tailWord_4946403, baseEnd_4946403] using wordTrace_append hprefix tailTrace_4946403
  have hstable : (prefixWord ++ tailWord_4946403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946403).length < 2 ^ (prefixWord ++ tailWord_4946403).sum := by decide
  have hdescent : baseEnd_4946403 < baseStart_4946403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946471 : List Nat := [1, 1, 7, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_4946471 : Nat := 118140960795 + 4946471 * 2 ^ 59
def prefixEnd_4946471 : Nat := 4983230072969 + 3 ^ 40 * 4946471 * 2
def baseEnd_4946471 : Nat := 2539917166526021643164101

theorem tailTrace_4946471 : CollatzResearch.WordTrace tailWord_4946471 prefixEnd_4946471 2539917166526021643164101 := by
  unfold tailWord_4946471
  simp only [CollatzResearch.WordTrace]
  refine ⟨180412618862787831834743267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120275079241858554556495511 180412618862787831834743267)
  ·
    refine ⟨270618928294181747752114901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180412618862787831834743267 270618928294181747752114901)
    ·
      refine ⟨6342631131894884712940193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 270618928294181747752114901 6342631131894884712940193)
      ·
        refine ⟨4756973348921163534705145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6342631131894884712940193 4756973348921163534705145)
        ·
          refine ⟨3567730011690872651028859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4756973348921163534705145 3567730011690872651028859)
          ·
            refine ⟨5351595017536308976543289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3567730011690872651028859 5351595017536308976543289)
            ·
              refine ⟨4013696263152231732407467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5351595017536308976543289 4013696263152231732407467)
              ·
                refine ⟨6020544394728347598611201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4013696263152231732407467 6020544394728347598611201)
                ·
                  refine ⟨4515408296046260698958401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6020544394728347598611201 4515408296046260698958401)
                  ·
                    refine ⟨3386556222034695524218801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4515408296046260698958401 3386556222034695524218801)
                    ·
                      refine ⟨2539917166526021643164101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3386556222034695524218801 2539917166526021643164101)
                      ·
                        rfl

theorem cell23_4946471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_4946471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946471 prefixEnd_4946471 := by exact prefixLift 4946471
  have htrace : WordTrace (prefixWord ++ tailWord_4946471) baseStart_4946471 baseEnd_4946471 := by
    simpa [prefixWord, tailWord_4946471, baseEnd_4946471] using wordTrace_append hprefix tailTrace_4946471
  have hstable : (prefixWord ++ tailWord_4946471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946471).length < 2 ^ (prefixWord ++ tailWord_4946471).sum := by decide
  have hdescent : baseEnd_4946471 < baseStart_4946471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946516 : List Nat := [2, 4, 1, 1, 1, 4, 2, 2, 6]
def baseStart_4946516 : Nat := 118140960795 + 4946516 * 2 ^ 59
def prefixEnd_4946516 : Nat := 4983230072969 + 3 ^ 40 * 4946516 * 2
def baseEnd_4946516 : Nat := 282215585906163774122377

theorem tailTrace_4946516 : CollatzResearch.WordTrace tailWord_4946516 prefixEnd_4946516 282215585906163774122377 := by
  unfold tailWord_4946516
  simp only [CollatzResearch.WordTrace]
  refine ⟨90207130073812402260065701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120276173431749869680087601 90207130073812402260065701)
  ·
    refine ⟨16913836888839825423762319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90207130073812402260065701 16913836888839825423762319)
    ·
      refine ⟨25370755333259738135643479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16913836888839825423762319 25370755333259738135643479)
      ·
        refine ⟨38056132999889607203465219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25370755333259738135643479 38056132999889607203465219)
        ·
          refine ⟨57084199499834410805197829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38056132999889607203465219 57084199499834410805197829)
          ·
            refine ⟨10703287406218952025974593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57084199499834410805197829 10703287406218952025974593)
            ·
              refine ⟨8027465554664214019480945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10703287406218952025974593 8027465554664214019480945)
              ·
                refine ⟨6020599165998160514610709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8027465554664214019480945 6020599165998160514610709)
                ·
                  refine ⟨282215585906163774122377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6020599165998160514610709 282215585906163774122377)
                  ·
                    rfl

theorem cell23_4946516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_4946516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946516 prefixEnd_4946516 := by exact prefixLift 4946516
  have htrace : WordTrace (prefixWord ++ tailWord_4946516) baseStart_4946516 baseEnd_4946516 := by
    simpa [prefixWord, tailWord_4946516, baseEnd_4946516] using wordTrace_append hprefix tailTrace_4946516
  have hstable : (prefixWord ++ tailWord_4946516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946516).length < 2 ^ (prefixWord ++ tailWord_4946516).sum := by decide
  have hdescent : baseEnd_4946516 < baseStart_4946516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946529 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 3, 5]
def baseStart_4946529 : Nat := 118140960795 + 4946529 * 2 ^ 59
def prefixEnd_4946529 : Nat := 4983230072969 + 3 ^ 40 * 4946529 * 2
def baseEnd_4946529 : Nat := 846648982801327472079611

theorem tailTrace_4946529 : CollatzResearch.WordTrace tailWord_4946529 prefixEnd_4946529 846648982801327472079611 := by
  unfold tailWord_4946529
  simp only [CollatzResearch.WordTrace]
  refine ⟨180414734296577707740354641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120276489531051805160236427 180414734296577707740354641)
  ·
    refine ⟨135311050722433280805265981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180414734296577707740354641 135311050722433280805265981)
    ·
      refine ⟨50741644020912480301974743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135311050722433280805265981 50741644020912480301974743)
      ·
        refine ⟨76112466031368720452962115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50741644020912480301974743 76112466031368720452962115)
        ·
          refine ⟨114168699047053080679443173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76112466031368720452962115 114168699047053080679443173)
          ·
            refine ⟨21406631071322452627395595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114168699047053080679443173 21406631071322452627395595)
            ·
              refine ⟨32109946606983678941093393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21406631071322452627395595 32109946606983678941093393)
              ·
                refine ⟨24082459955237759205820045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32109946606983678941093393 24082459955237759205820045)
                ·
                  refine ⟨9030922483214159702182517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24082459955237759205820045 9030922483214159702182517)
                  ·
                    refine ⟨846648982801327472079611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9030922483214159702182517 846648982801327472079611)
                    ·
                      rfl

theorem cell23_4946529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_4946529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946529 prefixEnd_4946529 := by exact prefixLift 4946529
  have htrace : WordTrace (prefixWord ++ tailWord_4946529) baseStart_4946529 baseEnd_4946529 := by
    simpa [prefixWord, tailWord_4946529, baseEnd_4946529] using wordTrace_append hprefix tailTrace_4946529
  have hstable : (prefixWord ++ tailWord_4946529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946529).length < 2 ^ (prefixWord ++ tailWord_4946529).sum := by decide
  have hdescent : baseEnd_4946529 < baseStart_4946529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946553 : List Nat := [1, 2, 1, 3, 3, 2, 3, 1, 2, 3, 2]
def baseStart_4946553 : Nat := 118140960795 + 4946553 * 2 ^ 59
def prefixEnd_4946553 : Nat := 4983230072969 + 3 ^ 40 * 4946553 * 2
def baseEnd_4946553 : Nat := 2539959271939690322338723

theorem tailTrace_4946553 : CollatzResearch.WordTrace tailWord_4946553 prefixEnd_4946553 2539959271939690322338723 := by
  unfold tailWord_4946553
  simp only [CollatzResearch.WordTrace]
  refine ⟨180415609648490759839228313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120277073098993839892818875 180415609648490759839228313)
  ·
    refine ⟨135311707236368069879421235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180415609648490759839228313 135311707236368069879421235)
    ·
      refine ⟨202967560854552104819131853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135311707236368069879421235 202967560854552104819131853)
      ·
        refine ⟨76112835320457039307174445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202967560854552104819131853 76112835320457039307174445)
        ·
          refine ⟨28542313245171389740190417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76112835320457039307174445 28542313245171389740190417)
          ·
            refine ⟨21406734933878542305142813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28542313245171389740190417 21406734933878542305142813)
            ·
              refine ⟨8027525600204453364428555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21406734933878542305142813 8027525600204453364428555)
              ·
                refine ⟨12041288400306680046642833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8027525600204453364428555 12041288400306680046642833)
                ·
                  refine ⟨9030966300230010034982125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12041288400306680046642833 9030966300230010034982125)
                  ·
                    refine ⟨3386612362586253763118297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9030966300230010034982125 3386612362586253763118297)
                    ·
                      refine ⟨2539959271939690322338723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3386612362586253763118297 2539959271939690322338723)
                      ·
                        rfl

theorem cell23_4946553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_4946553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946553 prefixEnd_4946553 := by exact prefixLift 4946553
  have htrace : WordTrace (prefixWord ++ tailWord_4946553) baseStart_4946553 baseEnd_4946553 := by
    simpa [prefixWord, tailWord_4946553, baseEnd_4946553] using wordTrace_append hprefix tailTrace_4946553
  have hstable : (prefixWord ++ tailWord_4946553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946553).length < 2 ^ (prefixWord ++ tailWord_4946553).sum := by decide
  have hdescent : baseEnd_4946553 < baseStart_4946553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946560 : List Nat := [2, 1, 1, 2, 1, 6, 2, 3, 1, 1, 3]
def baseStart_4946560 : Nat := 118140960795 + 4946560 * 2 ^ 59
def prefixEnd_4946560 : Nat := 4983230072969 + 3 ^ 40 * 4946560 * 2
def baseEnd_4946560 : Nat := 2539962866304271794951191

theorem tailTrace_4946560 : CollatzResearch.WordTrace tailWord_4946560 prefixEnd_4946560 2539962866304271794951191 := by
  unfold tailWord_4946560
  simp only [CollatzResearch.WordTrace]
  refine ⟨90207932479732700017366567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120277243306310266689822089 90207932479732700017366567)
  ·
    refine ⟨135311898719599050026049851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90207932479732700017366567 135311898719599050026049851)
    ·
      refine ⟨202967848079398575039074777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135311898719599050026049851 202967848079398575039074777)
      ·
        refine ⟨152225886059548931279306083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202967848079398575039074777 152225886059548931279306083)
        ·
          refine ⟨228338829089323396918959125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152225886059548931279306083 228338829089323396918959125)
          ·
            refine ⟨10703382613562034230576209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 228338829089323396918959125 10703382613562034230576209)
            ·
              refine ⟨8027536960171525672932157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10703382613562034230576209 8027536960171525672932157)
              ·
                refine ⟨3010326360064322127349559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8027536960171525672932157 3010326360064322127349559)
                ·
                  refine ⟨4515489540096483191024339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3010326360064322127349559 4515489540096483191024339)
                  ·
                    refine ⟨6773234310144724786536509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4515489540096483191024339 6773234310144724786536509)
                    ·
                      refine ⟨2539962866304271794951191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6773234310144724786536509 2539962866304271794951191)
                      ·
                        rfl

theorem cell23_4946560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 1, 1, 3].length) (baseStart_4946560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946560 prefixEnd_4946560 := by exact prefixLift 4946560
  have htrace : WordTrace (prefixWord ++ tailWord_4946560) baseStart_4946560 baseEnd_4946560 := by
    simpa [prefixWord, tailWord_4946560, baseEnd_4946560] using wordTrace_append hprefix tailTrace_4946560
  have hstable : (prefixWord ++ tailWord_4946560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946560).length < 2 ^ (prefixWord ++ tailWord_4946560).sum := by decide
  have hdescent : baseEnd_4946560 < baseStart_4946560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946569 : List Nat := [1, 2, 1, 1, 4, 1, 1, 5, 1, 1, 5]
def baseStart_4946569 : Nat := 118140960795 + 4946569 * 2 ^ 59
def prefixEnd_4946569 : Nat := 4983230072969 + 3 ^ 40 * 4946569 * 2
def baseEnd_4946569 : Nat := 2539967487630162259738649

theorem tailTrace_4946569 : CollatzResearch.WordTrace tailWord_4946569 prefixEnd_4946569 2539967487630162259738649 := by
  unfold tailWord_4946569
  simp only [CollatzResearch.WordTrace]
  refine ⟨180416193216432794571810761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120277462144288529714540507 180416193216432794571810761)
  ·
    refine ⟨135312144912324595928858071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180416193216432794571810761 135312144912324595928858071)
    ·
      refine ⟨202968217368486893893287107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135312144912324595928858071 202968217368486893893287107)
      ·
        refine ⟨304452326052730340839930661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202968217368486893893287107 304452326052730340839930661)
        ·
          refine ⟨57084811134886938907486999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 304452326052730340839930661 57084811134886938907486999)
          ·
            refine ⟨85627216702330408361230499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57084811134886938907486999 85627216702330408361230499)
            ·
              refine ⟨128440825053495612541845749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85627216702330408361230499 128440825053495612541845749)
              ·
                refine ⟨12041327348765213675798039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128440825053495612541845749 12041327348765213675798039)
                ·
                  refine ⟨18061991023147820513697059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12041327348765213675798039 18061991023147820513697059)
                  ·
                    refine ⟨27092986534721730770545589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18061991023147820513697059 27092986534721730770545589)
                    ·
                      refine ⟨2539967487630162259738649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27092986534721730770545589 2539967487630162259738649)
                      ·
                        rfl

theorem cell23_4946569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 1, 5].length) (baseStart_4946569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946569 prefixEnd_4946569 := by exact prefixLift 4946569
  have htrace : WordTrace (prefixWord ++ tailWord_4946569) baseStart_4946569 baseEnd_4946569 := by
    simpa [prefixWord, tailWord_4946569, baseEnd_4946569] using wordTrace_append hprefix tailTrace_4946569
  have hstable : (prefixWord ++ tailWord_4946569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946569).length < 2 ^ (prefixWord ++ tailWord_4946569).sum := by decide
  have hdescent : baseEnd_4946569 < baseStart_4946569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946593 : List Nat := [1, 2, 3, 3, 3, 2, 1, 1, 1, 6]
def baseStart_4946593 : Nat := 118140960795 + 4946593 * 2 ^ 59
def prefixEnd_4946593 : Nat := 4983230072969 + 3 ^ 40 * 4946593 * 2
def baseEnd_4946593 : Nat := 846659937055290055279513

theorem tailTrace_4946593 : CollatzResearch.WordTrace tailWord_4946593 prefixEnd_4946593 846659937055290055279513 := by
  unfold tailWord_4946593
  simp only [CollatzResearch.WordTrace]
  refine ⟨180417068568345846670684433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120278045712230564447122955 180417068568345846670684433)
  ·
    refine ⟨135312801426259385003013325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180417068568345846670684433 135312801426259385003013325)
    ·
      refine ⟨50742300534847269376129997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135312801426259385003013325 50742300534847269376129997)
      ·
        refine ⟨19028362700567726016048749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50742300534847269376129997 19028362700567726016048749)
        ·
          refine ⟨7135636012712897256018281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19028362700567726016048749 7135636012712897256018281)
          ·
            refine ⟨5351727009534672942013711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7135636012712897256018281 5351727009534672942013711)
            ·
              refine ⟨8027590514302009413020567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5351727009534672942013711 8027590514302009413020567)
              ·
                refine ⟨12041385771453014119530851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8027590514302009413020567 12041385771453014119530851)
                ·
                  refine ⟨18062078657179521179296277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12041385771453014119530851 18062078657179521179296277)
                  ·
                    refine ⟨846659937055290055279513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18062078657179521179296277 846659937055290055279513)
                    ·
                      rfl

theorem cell23_4946593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_4946593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946593 prefixEnd_4946593 := by exact prefixLift 4946593
  have htrace : WordTrace (prefixWord ++ tailWord_4946593) baseStart_4946593 baseEnd_4946593 := by
    simpa [prefixWord, tailWord_4946593, baseEnd_4946593] using wordTrace_append hprefix tailTrace_4946593
  have hstable : (prefixWord ++ tailWord_4946593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946593).length < 2 ^ (prefixWord ++ tailWord_4946593).sum := by decide
  have hdescent : baseEnd_4946593 < baseStart_4946593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946634 : List Nat := [3, 1, 2, 1, 4, 2, 3, 2, 1, 2, 2]
def baseStart_4946634 : Nat := 118140960795 + 4946634 * 2 ^ 59
def prefixEnd_4946634 : Nat := 4983230072969 + 3 ^ 40 * 4946634 * 2
def baseEnd_4946634 : Nat := 2540000863872704505425851

theorem tailTrace_4946634 : CollatzResearch.WordTrace tailWord_4946634 prefixEnd_4946634 2540000863872704505425851 := by
  unfold tailWord_4946634
  simp only [CollatzResearch.WordTrace]
  refine ⟨45104640990299327668231739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120279042640798207115284637 45104640990299327668231739)
  ·
    refine ⟨67656961485448991502347609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45104640990299327668231739 67656961485448991502347609)
    ·
      refine ⟨50742721114086743626760707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67656961485448991502347609 50742721114086743626760707)
      ·
        refine ⟨76114081671130115440141061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50742721114086743626760707 76114081671130115440141061)
        ·
          refine ⟨14271390313336896645026449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76114081671130115440141061 14271390313336896645026449)
          ·
            refine ⟨10703542735002672483769837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14271390313336896645026449 10703542735002672483769837)
            ·
              refine ⟨4013828525626002181413689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10703542735002672483769837 4013828525626002181413689)
              ·
                refine ⟨3010371394219501636060267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4013828525626002181413689 3010371394219501636060267)
                ·
                  refine ⟨4515557091329252454090401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3010371394219501636060267 4515557091329252454090401)
                  ·
                    refine ⟨3386667818496939340567801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4515557091329252454090401 3386667818496939340567801)
                    ·
                      refine ⟨2540000863872704505425851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3386667818496939340567801 2540000863872704505425851)
                      ·
                        rfl

theorem cell23_4946634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 1, 2, 2].length) (baseStart_4946634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946634 prefixEnd_4946634 := by exact prefixLift 4946634
  have htrace : WordTrace (prefixWord ++ tailWord_4946634) baseStart_4946634 baseEnd_4946634 := by
    simpa [prefixWord, tailWord_4946634, baseEnd_4946634] using wordTrace_append hprefix tailTrace_4946634
  have hstable : (prefixWord ++ tailWord_4946634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946634).length < 2 ^ (prefixWord ++ tailWord_4946634).sum := by decide
  have hdescent : baseEnd_4946634 < baseStart_4946634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946644 : List Nat := [2, 4, 1, 3, 3, 1, 2, 1, 2, 4]
def baseStart_4946644 : Nat := 118140960795 + 4946644 * 2 ^ 59
def prefixEnd_4946644 : Nat := 4983230072969 + 3 ^ 40 * 4946644 * 2
def baseEnd_4946644 : Nat := 846668666226416488766935

theorem tailTrace_4946644 : CollatzResearch.WordTrace tailWord_4946644 prefixEnd_4946644 846668666226416488766935 := by
  unfold tailWord_4946644
  simp only [CollatzResearch.WordTrace]
  refine ⟨90209464345580541190395493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120279285794107388253860657 90209464345580541190395493)
  ·
    refine ⟨16914274564796351473199155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90209464345580541190395493 16914274564796351473199155)
    ·
      refine ⟨25371411847194527209798733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16914274564796351473199155 25371411847194527209798733)
      ·
        refine ⟨9514279442697947703674525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25371411847194527209798733 9514279442697947703674525)
        ·
          refine ⟨3567854791011730388877947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9514279442697947703674525 3567854791011730388877947)
          ·
            refine ⟨5351782186517595583316921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3567854791011730388877947 5351782186517595583316921)
            ·
              refine ⟨4013836639888196687487691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5351782186517595583316921 4013836639888196687487691)
              ·
                refine ⟨6020754959832295031231537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4013836639888196687487691 6020754959832295031231537)
                ·
                  refine ⟨4515566219874221273423653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6020754959832295031231537 4515566219874221273423653)
                  ·
                    refine ⟨846668666226416488766935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4515566219874221273423653 846668666226416488766935)
                    ·
                      rfl

theorem cell23_4946644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_4946644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946644 prefixEnd_4946644 := by exact prefixLift 4946644
  have htrace : WordTrace (prefixWord ++ tailWord_4946644) baseStart_4946644 baseEnd_4946644 := by
    simpa [prefixWord, tailWord_4946644, baseEnd_4946644] using wordTrace_append hprefix tailTrace_4946644
  have hstable : (prefixWord ++ tailWord_4946644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946644).length < 2 ^ (prefixWord ++ tailWord_4946644).sum := by decide
  have hdescent : baseEnd_4946644 < baseStart_4946644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946649 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 1, 8]
def baseStart_4946649 : Nat := 118140960795 + 4946649 * 2 ^ 59
def prefixEnd_4946649 : Nat := 4983230072969 + 3 ^ 40 * 4946649 * 2
def baseEnd_4946649 : Nat := 846669522027507315579427

theorem tailTrace_4946649 : CollatzResearch.WordTrace tailWord_4946649 prefixEnd_4946649 846669522027507315579427 := by
  unfold tailWord_4946649
  simp only [CollatzResearch.WordTrace]
  refine ⟨180419111056142968234723001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120279407370761978823148667 180419111056142968234723001)
  ·
    refine ⟨135314333292107226176042251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180419111056142968234723001 135314333292107226176042251)
    ·
      refine ⟨202971499938160839264063377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135314333292107226176042251 202971499938160839264063377)
      ·
        refine ⟨152228624953620629448047533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202971499938160839264063377 152228624953620629448047533)
        ·
          refine ⟨57085734357607736043017825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152228624953620629448047533 57085734357607736043017825)
          ·
            refine ⟨42814300768205802032263369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57085734357607736043017825 42814300768205802032263369)
            ·
              refine ⟨32110725576154351524197527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42814300768205802032263369 32110725576154351524197527)
              ·
                refine ⟨48166088364231527286296291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32110725576154351524197527 48166088364231527286296291)
                ·
                  refine ⟨72249132546347290929444437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48166088364231527286296291 72249132546347290929444437)
                  ·
                    refine ⟨846669522027507315579427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72249132546347290929444437 846669522027507315579427)
                    ·
                      rfl

theorem cell23_4946649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 8].length) (baseStart_4946649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946649 prefixEnd_4946649 := by exact prefixLift 4946649
  have htrace : WordTrace (prefixWord ++ tailWord_4946649) baseStart_4946649 baseEnd_4946649 := by
    simpa [prefixWord, tailWord_4946649, baseEnd_4946649] using wordTrace_append hprefix tailTrace_4946649
  have hstable : (prefixWord ++ tailWord_4946649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946649).length < 2 ^ (prefixWord ++ tailWord_4946649).sum := by decide
  have hdescent : baseEnd_4946649 < baseStart_4946649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946660 : List Nat := [2, 3, 1, 1, 1, 4, 3, 2, 1, 3, 2]
def baseStart_4946660 : Nat := 118140960795 + 4946660 * 2 ^ 59
def prefixEnd_4946660 : Nat := 4983230072969 + 3 ^ 40 * 4946660 * 2
def baseEnd_4946660 : Nat := 2540014214369721403700731

theorem tailTrace_4946660 : CollatzResearch.WordTrace tailWord_4946660 prefixEnd_4946660 2540014214369721403700731 := by
  unfold tailWord_4946660
  simp only [CollatzResearch.WordTrace]
  refine ⟨90209756129551558556686717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120279674839402078075582289 90209756129551558556686717)
  ·
    refine ⟨33828658548581834458757519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90209756129551558556686717 33828658548581834458757519)
    ·
      refine ⟨50742987822872751688136279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33828658548581834458757519 50742987822872751688136279)
      ·
        refine ⟨76114481734309127532204419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50742987822872751688136279 76114481734309127532204419)
        ·
          refine ⟨114171722601463691298306629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76114481734309127532204419 114171722601463691298306629)
          ·
            refine ⟨21407197987774442118432493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114171722601463691298306629 21407197987774442118432493)
            ·
              refine ⟨8027699245415415794412185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21407197987774442118432493 8027699245415415794412185)
              ·
                refine ⟨6020774434061561845809139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8027699245415415794412185 6020774434061561845809139)
                ·
                  refine ⟨9031161651092342768713709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6020774434061561845809139 9031161651092342768713709)
                  ·
                    refine ⟨3386685619159628538267641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9031161651092342768713709 3386685619159628538267641)
                    ·
                      refine ⟨2540014214369721403700731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3386685619159628538267641 2540014214369721403700731)
                      ·
                        rfl

theorem cell23_4946660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_4946660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946660 prefixEnd_4946660 := by exact prefixLift 4946660
  have htrace : WordTrace (prefixWord ++ tailWord_4946660) baseStart_4946660 baseEnd_4946660 := by
    simpa [prefixWord, tailWord_4946660, baseEnd_4946660] using wordTrace_append hprefix tailTrace_4946660
  have hstable : (prefixWord ++ tailWord_4946660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946660).length < 2 ^ (prefixWord ++ tailWord_4946660).sum := by decide
  have hdescent : baseEnd_4946660 < baseStart_4946660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946673 : List Nat := [1, 2, 2, 2, 2, 2, 3, 2, 1, 4, 2]
def baseStart_4946673 : Nat := 118140960795 + 4946673 * 2 ^ 59
def prefixEnd_4946673 : Nat := 4983230072969 + 3 ^ 40 * 4946673 * 2
def baseEnd_4946673 : Nat := 2540020889618229852838171

theorem tailTrace_4946673 : CollatzResearch.WordTrace tailWord_4946673 prefixEnd_4946673 2540020889618229852838171 := by
  unfold tailWord_4946673
  simp only [CollatzResearch.WordTrace]
  refine ⟨180419986408056020333596673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120279990938704013555731115 180419986408056020333596673)
  ·
    refine ⟨135314989806042015250197505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180419986408056020333596673 135314989806042015250197505)
    ·
      refine ⟨101486242354531511437648129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135314989806042015250197505 101486242354531511437648129)
      ·
        refine ⟨76114681765898633578236097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101486242354531511437648129 76114681765898633578236097)
        ·
          refine ⟨57086011324423975183677073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76114681765898633578236097 57086011324423975183677073)
          ·
            refine ⟨42814508493317981387757805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57086011324423975183677073 42814508493317981387757805)
            ·
              refine ⟨16055440684994243020409177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42814508493317981387757805 16055440684994243020409177)
              ·
                refine ⟨12041580513745682265306883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16055440684994243020409177 12041580513745682265306883)
                ·
                  refine ⟨18062370770618523397960325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12041580513745682265306883 18062370770618523397960325)
                  ·
                    refine ⟨3386694519490973137117561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18062370770618523397960325 3386694519490973137117561)
                    ·
                      refine ⟨2540020889618229852838171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3386694519490973137117561 2540020889618229852838171)
                      ·
                        rfl

theorem cell23_4946673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_4946673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946673 prefixEnd_4946673 := by exact prefixLift 4946673
  have htrace : WordTrace (prefixWord ++ tailWord_4946673) baseStart_4946673 baseEnd_4946673 := by
    simpa [prefixWord, tailWord_4946673, baseEnd_4946673] using wordTrace_append hprefix tailTrace_4946673
  have hstable : (prefixWord ++ tailWord_4946673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946673).length < 2 ^ (prefixWord ++ tailWord_4946673).sum := by decide
  have hdescent : baseEnd_4946673 < baseStart_4946673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946699 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 8]
def baseStart_4946699 : Nat := 118140960795 + 4946699 * 2 ^ 59
def prefixEnd_4946699 : Nat := 4983230072969 + 3 ^ 40 * 4946699 * 2
def baseEnd_4946699 : Nat := 2540034240115246751113051

theorem tailTrace_4946699 : CollatzResearch.WordTrace tailWord_4946699 prefixEnd_4946699 2540034240115246751113051 := by
  unfold tailWord_4946699
  simp only [CollatzResearch.WordTrace]
  refine ⟨180420934705961826774043151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120280623137307884516028767 180420934705961826774043151)
  ·
    refine ⟨270631402058942740161064727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180420934705961826774043151 270631402058942740161064727)
    ·
      refine ⟨405947103088414110241597091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270631402058942740161064727 405947103088414110241597091)
      ·
        refine ⟨608920654632621165362395637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405947103088414110241597091 608920654632621165362395637)
        ·
          refine ⟨57086311371808234252724591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 608920654632621165362395637 57086311371808234252724591)
          ·
            refine ⟨85629467057712351379086887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57086311371808234252724591 85629467057712351379086887)
            ·
              refine ⟨128444200586568527068630331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85629467057712351379086887 128444200586568527068630331)
              ·
                refine ⟨192666300879852790602945497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128444200586568527068630331 192666300879852790602945497)
                ·
                  refine ⟨144499725659889592952209123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192666300879852790602945497 144499725659889592952209123)
                  ·
                    refine ⟨216749588489834389428313685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 144499725659889592952209123 216749588489834389428313685)
                    ·
                      refine ⟨2540034240115246751113051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 216749588489834389428313685 2540034240115246751113051)
                      ·
                        rfl

theorem cell23_4946699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 8].length) (baseStart_4946699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946699 prefixEnd_4946699 := by exact prefixLift 4946699
  have htrace : WordTrace (prefixWord ++ tailWord_4946699) baseStart_4946699 baseEnd_4946699 := by
    simpa [prefixWord, tailWord_4946699, baseEnd_4946699] using wordTrace_append hprefix tailTrace_4946699
  have hstable : (prefixWord ++ tailWord_4946699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946699).length < 2 ^ (prefixWord ++ tailWord_4946699).sum := by decide
  have hdescent : baseEnd_4946699 < baseStart_4946699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946758 : List Nat := [6, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_4946758 : Nat := 118140960795 + 4946758 * 2 ^ 59
def prefixEnd_4946758 : Nat := 4983230072969 + 3 ^ 40 * 4946758 * 2
def baseEnd_4946758 : Nat := 2540064535473862020275281

theorem tailTrace_4946758 : CollatzResearch.WordTrace tailWord_4946758 prefixEnd_4946758 2540064535473862020275281 := by
  unfold tailWord_4946758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5638221456648377495326279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 120282057741832053233627285 5638221456648377495326279)
  ·
    refine ⟨8457332184972566242989419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5638221456648377495326279 8457332184972566242989419)
    ·
      refine ⟨12685998277458849364484129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8457332184972566242989419 12685998277458849364484129)
      ·
        refine ⟨9514498708094137023363097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12685998277458849364484129 9514498708094137023363097)
        ·
          refine ⟨7135874031070602767522323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9514498708094137023363097 7135874031070602767522323)
          ·
            refine ⟨10703811046605904151283485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7135874031070602767522323 10703811046605904151283485)
            ·
              refine ⟨4013929142477214056731307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10703811046605904151283485 4013929142477214056731307)
              ·
                refine ⟨6020893713715821085096961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4013929142477214056731307 6020893713715821085096961)
                ·
                  refine ⟨4515670285286865813822721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6020893713715821085096961 4515670285286865813822721)
                  ·
                    refine ⟨3386752713965149360367041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4515670285286865813822721 3386752713965149360367041)
                    ·
                      refine ⟨2540064535473862020275281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3386752713965149360367041 2540064535473862020275281)
                      ·
                        rfl

theorem cell23_4946758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_4946758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946758 prefixEnd_4946758 := by exact prefixLift 4946758
  have htrace : WordTrace (prefixWord ++ tailWord_4946758) baseStart_4946758 baseEnd_4946758 := by
    simpa [prefixWord, tailWord_4946758, baseEnd_4946758] using wordTrace_append hprefix tailTrace_4946758
  have hstable : (prefixWord ++ tailWord_4946758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946758).length < 2 ^ (prefixWord ++ tailWord_4946758).sum := by decide
  have hdescent : baseEnd_4946758 < baseStart_4946758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946773 : List Nat := [1, 3, 2, 2, 2, 1, 1, 4, 3, 4]
def baseStart_4946773 : Nat := 118140960795 + 4946773 * 2 ^ 59
def prefixEnd_4946773 : Nat := 4983230072969 + 3 ^ 40 * 4946773 * 2
def baseEnd_4946773 : Nat := 846690745894559820529237

theorem tailTrace_4946773 : CollatzResearch.WordTrace tailWord_4946773 prefixEnd_4946773 846690745894559820529237 := by
  unfold tailWord_4946773
  simp only [CollatzResearch.WordTrace]
  refine ⟨180423633707693737412236973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120282422471795824941491315 180423633707693737412236973)
  ·
    refine ⟨67658862640385151529588865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180423633707693737412236973 67658862640385151529588865)
    ·
      refine ⟨50744146980288863647191649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67658862640385151529588865 50744146980288863647191649)
      ·
        refine ⟨38058110235216647735393737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50744146980288863647191649 38058110235216647735393737)
        ·
          refine ⟨28543582676412485801545303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38058110235216647735393737 28543582676412485801545303)
          ·
            refine ⟨42815374014618728702317955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28543582676412485801545303 42815374014618728702317955)
            ·
              refine ⟨64223061021928093053476933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42815374014618728702317955 64223061021928093053476933)
              ·
                refine ⟨12041823941611517447526925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64223061021928093053476933 12041823941611517447526925)
                ·
                  refine ⟨4515683978104319042822597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12041823941611517447526925 4515683978104319042822597)
                  ·
                    refine ⟨846690745894559820529237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4515683978104319042822597 846690745894559820529237)
                    ·
                      rfl

theorem cell23_4946773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_4946773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946773 prefixEnd_4946773 := by exact prefixLift 4946773
  have htrace : WordTrace (prefixWord ++ tailWord_4946773) baseStart_4946773 baseEnd_4946773 := by
    simpa [prefixWord, tailWord_4946773, baseEnd_4946773] using wordTrace_append hprefix tailTrace_4946773
  have hstable : (prefixWord ++ tailWord_4946773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946773).length < 2 ^ (prefixWord ++ tailWord_4946773).sum := by decide
  have hdescent : baseEnd_4946773 < baseStart_4946773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946783 : List Nat := [1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 3]
def baseStart_4946783 : Nat := 118140960795 + 4946783 * 2 ^ 59
def prefixEnd_4946783 : Nat := 4983230072969 + 3 ^ 40 * 4946783 * 2
def baseEnd_4946783 : Nat := 2540077372490224422462665

theorem tailTrace_4946783 : CollatzResearch.WordTrace tailWord_4946783 prefixEnd_4946783 2540077372490224422462665 := by
  unfold tailWord_4946783
  simp only [CollatzResearch.WordTrace]
  refine ⟨180423998437657509120101003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120282665625105006080067335 180423998437657509120101003)
  ·
    refine ⟨270635997656486263680151505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180423998437657509120101003 270635997656486263680151505)
    ·
      refine ⟨202976998242364697760113629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270635997656486263680151505 202976998242364697760113629)
      ·
        refine ⟨76116374340886761660042611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202976998242364697760113629 76116374340886761660042611)
        ·
          refine ⟨114174561511330142490063917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76116374340886761660042611 114174561511330142490063917)
          ·
            refine ⟨42815460566748803433773969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114174561511330142490063917 42815460566748803433773969)
            ·
              refine ⟨32111595425061602575330477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42815460566748803433773969 32111595425061602575330477)
              ·
                refine ⟨12041848284398100965748929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32111595425061602575330477 12041848284398100965748929)
                ·
                  refine ⟨9031386213298575724311697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12041848284398100965748929 9031386213298575724311697)
                  ·
                    refine ⟨6773539659973931793233773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9031386213298575724311697 6773539659973931793233773)
                    ·
                      refine ⟨2540077372490224422462665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6773539659973931793233773 2540077372490224422462665)
                      ·
                        rfl

theorem cell23_4946783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_4946783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946783 prefixEnd_4946783 := by exact prefixLift 4946783
  have htrace : WordTrace (prefixWord ++ tailWord_4946783) baseStart_4946783 baseEnd_4946783 := by
    simpa [prefixWord, tailWord_4946783, baseEnd_4946783] using wordTrace_append hprefix tailTrace_4946783
  have hstable : (prefixWord ++ tailWord_4946783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946783).length < 2 ^ (prefixWord ++ tailWord_4946783).sum := by decide
  have hdescent : baseEnd_4946783 < baseStart_4946783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946880 : List Nat := [2, 1, 1, 2, 3, 3, 2, 3, 2, 4]
def baseStart_4946880 : Nat := 118140960795 + 4946880 * 2 ^ 59
def prefixEnd_4946880 : Nat := 4983230072969 + 3 ^ 40 * 4946880 * 2
def baseEnd_4946880 : Nat := 846709060037903514316573

theorem tailTrace_4946880 : CollatzResearch.WordTrace tailWord_4946880 prefixEnd_4946880 846709060037903514316573 := by
  unfold tailWord_4946880
  simp only [CollatzResearch.WordTrace]
  refine ⟨90213768159153047343191047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120285024212204063124254729 90213768159153047343191047)
  ·
    refine ⟨135320652238729571014786571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90213768159153047343191047 135320652238729571014786571)
    ·
      refine ⟨202980978358094356522179857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135320652238729571014786571 202980978358094356522179857)
      ·
        refine ⟨152235733768570767391634893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202980978358094356522179857 152235733768570767391634893)
        ·
          refine ⟨57088400163214037771863085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152235733768570767391634893 57088400163214037771863085)
          ·
            refine ⟨21408150061205264164448657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57088400163214037771863085 21408150061205264164448657)
            ·
              refine ⟨16056112545903948123336493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21408150061205264164448657 16056112545903948123336493)
              ·
                refine ⟨6021042204713980546251185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16056112545903948123336493 6021042204713980546251185)
                ·
                  refine ⟨4515781653535485409688389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6021042204713980546251185 4515781653535485409688389)
                  ·
                    refine ⟨846709060037903514316573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4515781653535485409688389 846709060037903514316573)
                    ·
                      rfl

theorem cell23_4946880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 2, 4].length) (baseStart_4946880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946880 prefixEnd_4946880 := by exact prefixLift 4946880
  have htrace : WordTrace (prefixWord ++ tailWord_4946880) baseStart_4946880 baseEnd_4946880 := by
    simpa [prefixWord, tailWord_4946880, baseEnd_4946880] using wordTrace_append hprefix tailTrace_4946880
  have hstable : (prefixWord ++ tailWord_4946880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946880).length < 2 ^ (prefixWord ++ tailWord_4946880).sum := by decide
  have hdescent : baseEnd_4946880 < baseStart_4946880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946890 : List Nat := [3, 1, 2, 1, 2, 1, 1, 6, 1, 2, 3]
def baseStart_4946890 : Nat := 118140960795 + 4946890 * 2 ^ 59
def prefixEnd_4946890 : Nat := 4983230072969 + 3 ^ 40 * 4946890 * 2
def baseEnd_4946890 : Nat := 2540132314920255503824673

theorem tailTrace_4946890 : CollatzResearch.WordTrace tailWord_4946890 prefixEnd_4946890 2540132314920255503824673 := by
  unfold tailWord_4946890
  simp only [CollatzResearch.WordTrace]
  refine ⟨45106975262067466598561531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120285267365513244262830749 45106975262067466598561531)
  ·
    refine ⟨67660462893101199897842297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45106975262067466598561531 67660462893101199897842297)
    ·
      refine ⟨50745347169825899923381723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67660462893101199897842297 50745347169825899923381723)
      ·
        refine ⟨76118020754738849885072585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50745347169825899923381723 76118020754738849885072585)
        ·
          refine ⟨57088515566054137413804439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76118020754738849885072585 57088515566054137413804439)
          ·
            refine ⟨85632773349081206120706659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57088515566054137413804439 85632773349081206120706659)
            ·
              refine ⟨128449160023621809181059989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85632773349081206120706659 128449160023621809181059989)
              ·
                refine ⟨6021054376107272305362187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 128449160023621809181059989 6021054376107272305362187)
                ·
                  refine ⟨9031581564160908458043281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6021054376107272305362187 9031581564160908458043281)
                  ·
                    refine ⟨6773686173120681343532461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9031581564160908458043281 6773686173120681343532461)
                    ·
                      refine ⟨2540132314920255503824673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6773686173120681343532461 2540132314920255503824673)
                      ·
                        rfl

theorem cell23_4946890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_4946890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946890 prefixEnd_4946890 := by exact prefixLift 4946890
  have htrace : WordTrace (prefixWord ++ tailWord_4946890) baseStart_4946890 baseEnd_4946890 := by
    simpa [prefixWord, tailWord_4946890, baseEnd_4946890] using wordTrace_append hprefix tailTrace_4946890
  have hstable : (prefixWord ++ tailWord_4946890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946890).length < 2 ^ (prefixWord ++ tailWord_4946890).sum := by decide
  have hdescent : baseEnd_4946890 < baseStart_4946890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946900 : List Nat := [2, 4, 1, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_4946900 : Nat := 118140960795 + 4946900 * 2 ^ 59
def prefixEnd_4946900 : Nat := 4983230072969 + 3 ^ 40 * 4946900 * 2
def baseEnd_4946900 : Nat := 2540137449726800464699627

theorem tailTrace_4946900 : CollatzResearch.WordTrace tailWord_4946900 prefixEnd_4946900 2540137449726800464699627 := by
  unfold tailWord_4946900
  simp only [CollatzResearch.WordTrace]
  refine ⟨90214132889116819051055077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120285510518822425401406769 90214132889116819051055077)
  ·
    refine ⟨16915149916709403572072827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90214132889116819051055077 16915149916709403572072827)
    ·
      refine ⟨25372724875064105358109241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16915149916709403572072827 25372724875064105358109241)
      ·
        refine ⟨19029543656298079018581931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25372724875064105358109241 19029543656298079018581931)
        ·
          refine ⟨28544315484447118527872897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19029543656298079018581931 28544315484447118527872897)
          ·
            refine ⟨21408236613335338895904673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28544315484447118527872897 21408236613335338895904673)
            ·
              refine ⟨16056177460001504171928505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21408236613335338895904673 16056177460001504171928505)
              ·
                refine ⟨12042133095001128128946379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16056177460001504171928505 12042133095001128128946379)
                ·
                  refine ⟨18063199642501692193419569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12042133095001128128946379 18063199642501692193419569)
                  ·
                    refine ⟨13547399731876269145064677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18063199642501692193419569 13547399731876269145064677)
                    ·
                      refine ⟨2540137449726800464699627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13547399731876269145064677 2540137449726800464699627)
                      ·
                        rfl

theorem cell23_4946900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_4946900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946900 prefixEnd_4946900 := by exact prefixLift 4946900
  have htrace : WordTrace (prefixWord ++ tailWord_4946900) baseStart_4946900 baseEnd_4946900 := by
    simpa [prefixWord, tailWord_4946900, baseEnd_4946900] using wordTrace_append hprefix tailTrace_4946900
  have hstable : (prefixWord ++ tailWord_4946900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946900).length < 2 ^ (prefixWord ++ tailWord_4946900).sum := by decide
  have hdescent : baseEnd_4946900 < baseStart_4946900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946903 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 3]
def baseStart_4946903 : Nat := 118140960795 + 4946903 * 2 ^ 59
def prefixEnd_4946903 : Nat := 4983230072969 + 3 ^ 40 * 4946903 * 2
def baseEnd_4946903 : Nat := 2540138990168763952962113

theorem tailTrace_4946903 : CollatzResearch.WordTrace tailWord_4946903 prefixEnd_4946903 2540138990168763952962113 := by
  unfold tailWord_4946903
  simp only [CollatzResearch.WordTrace]
  refine ⟨180428375197222769614469363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120285583464815179742979575 180428375197222769614469363)
  ·
    refine ⟨270642562795834154421704045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180428375197222769614469363 270642562795834154421704045)
    ·
      refine ⟨101490961048437807908139017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270642562795834154421704045 101490961048437807908139017)
      ·
        refine ⟨76118220786328355931104263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101490961048437807908139017 76118220786328355931104263)
        ·
          refine ⟨114177331179492533896656395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76118220786328355931104263 114177331179492533896656395)
          ·
            refine ⟨171265996769238800844984593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114177331179492533896656395 171265996769238800844984593)
            ·
              refine ⟨128449497576929100633738445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171265996769238800844984593 128449497576929100633738445)
              ·
                refine ⟨48168561591348412737651917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128449497576929100633738445 48168561591348412737651917)
                ·
                  refine ⟨18063210596755654776619469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48168561591348412737651917 18063210596755654776619469)
                  ·
                    refine ⟨6773703973783370541232301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18063210596755654776619469 6773703973783370541232301)
                    ·
                      refine ⟨2540138990168763952962113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6773703973783370541232301 2540138990168763952962113)
                      ·
                        rfl

theorem cell23_4946903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_4946903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946903 prefixEnd_4946903 := by exact prefixLift 4946903
  have htrace : WordTrace (prefixWord ++ tailWord_4946903) baseStart_4946903 baseEnd_4946903 := by
    simpa [prefixWord, tailWord_4946903, baseEnd_4946903] using wordTrace_append hprefix tailTrace_4946903
  have hstable : (prefixWord ++ tailWord_4946903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946903).length < 2 ^ (prefixWord ++ tailWord_4946903).sum := by decide
  have hdescent : baseEnd_4946903 < baseStart_4946903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946904 : List Nat := [2, 1, 2, 2, 2, 3, 1, 5, 1, 2, 2]
def baseStart_4946904 : Nat := 118140960795 + 4946904 * 2 ^ 59
def prefixEnd_4946904 : Nat := 4983230072969 + 3 ^ 40 * 4946904 * 2
def baseEnd_4946904 : Nat := 2540139503649418449049609

theorem tailTrace_4946904 : CollatzResearch.WordTrace tailWord_4946904 prefixEnd_4946904 2540139503649418449049609 := by
  unfold tailWord_4946904
  simp only [CollatzResearch.WordTrace]
  refine ⟨90214205835109573392627883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120285607780146097856837177 90214205835109573392627883)
  ·
    refine ⟨135321308752664360088941825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90214205835109573392627883 135321308752664360088941825)
    ·
      refine ⟨101490981564498270066706369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135321308752664360088941825 101490981564498270066706369)
      ·
        refine ⟨76118236173373702550029777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101490981564498270066706369 76118236173373702550029777)
        ·
          refine ⟨57088677130030276912522333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76118236173373702550029777 57088677130030276912522333)
          ·
            refine ⟨21408253923761353842195875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57088677130030276912522333 21408253923761353842195875)
            ·
              refine ⟨32112380885642030763293813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21408253923761353842195875 32112380885642030763293813)
              ·
                refine ⟨3010535708028940384058795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32112380885642030763293813 3010535708028940384058795)
                ·
                  refine ⟨4515803562043410576088193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3010535708028940384058795 4515803562043410576088193)
                  ·
                    refine ⟨3386852671532557932066145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4515803562043410576088193 3386852671532557932066145)
                    ·
                      refine ⟨2540139503649418449049609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3386852671532557932066145 2540139503649418449049609)
                      ·
                        rfl

theorem cell23_4946904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 1, 2, 2].length) (baseStart_4946904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946904 prefixEnd_4946904 := by exact prefixLift 4946904
  have htrace : WordTrace (prefixWord ++ tailWord_4946904) baseStart_4946904 baseEnd_4946904 := by
    simpa [prefixWord, tailWord_4946904, baseEnd_4946904] using wordTrace_append hprefix tailTrace_4946904
  have hstable : (prefixWord ++ tailWord_4946904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946904).length < 2 ^ (prefixWord ++ tailWord_4946904).sum := by decide
  have hdescent : baseEnd_4946904 < baseStart_4946904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946914 : List Nat := [3, 3, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_4946914 : Nat := 118140960795 + 4946914 * 2 ^ 59
def prefixEnd_4946914 : Nat := 4983230072969 + 3 ^ 40 * 4946914 * 2
def baseEnd_4946914 : Nat := 846714879485321136641521

theorem tailTrace_4946914 : CollatzResearch.WordTrace tailWord_4946914 prefixEnd_4946914 846714879485321136641521 := by
  unfold tailWord_4946914
  simp only [CollatzResearch.WordTrace]
  refine ⟨45107194100045729623279949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120285850933455278995413197 45107194100045729623279949)
  ·
    refine ⟨16915197787517148608729981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45107194100045729623279949 16915197787517148608729981)
    ·
      refine ⟨6343199170318930728273743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16915197787517148608729981 6343199170318930728273743)
      ·
        refine ⟨9514798755478396092410615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6343199170318930728273743 9514798755478396092410615)
        ·
          refine ⟨14272198133217594138615923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9514798755478396092410615 14272198133217594138615923)
          ·
            refine ⟨21408297199826391207923885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14272198133217594138615923 21408297199826391207923885)
            ·
              refine ⟨8028111449934896702971457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21408297199826391207923885 8028111449934896702971457)
              ·
                refine ⟨6021083587451172527228593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8028111449934896702971457 6021083587451172527228593)
                ·
                  refine ⟨4515812690588379395421445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6021083587451172527228593 4515812690588379395421445)
                  ·
                    refine ⟨846714879485321136641521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4515812690588379395421445 846714879485321136641521)
                    ·
                      rfl

theorem cell23_4946914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_4946914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946914 prefixEnd_4946914 := by exact prefixLift 4946914
  have htrace : WordTrace (prefixWord ++ tailWord_4946914) baseStart_4946914 baseEnd_4946914 := by
    simpa [prefixWord, tailWord_4946914, baseEnd_4946914] using wordTrace_append hprefix tailTrace_4946914
  have hstable : (prefixWord ++ tailWord_4946914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946914).length < 2 ^ (prefixWord ++ tailWord_4946914).sum := by decide
  have hdescent : baseEnd_4946914 < baseStart_4946914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946963 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 3]
def baseStart_4946963 : Nat := 118140960795 + 4946963 * 2 ^ 59
def prefixEnd_4946963 : Nat := 4983230072969 + 3 ^ 40 * 4946963 * 2
def baseEnd_4946963 : Nat := 2540169799008033718211837

theorem tailTrace_4946963 : CollatzResearch.WordTrace tailWord_4946963 prefixEnd_4946963 2540169799008033718211837 := by
  unfold tailWord_4946963
  simp only [CollatzResearch.WordTrace]
  refine ⟨180430563577005399861653543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120287042384670266574435695 180430563577005399861653543)
  ·
    refine ⟨270645845365508099792480315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180430563577005399861653543 270645845365508099792480315)
    ·
      refine ⟨405968768048262149688720473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270645845365508099792480315 405968768048262149688720473)
      ·
        refine ⟨304476576036196612266540355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 405968768048262149688720473 304476576036196612266540355)
        ·
          refine ⟨456714864054294918399810533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304476576036196612266540355 456714864054294918399810533)
          ·
            refine ⟨85634037010180297199964475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 456714864054294918399810533 85634037010180297199964475)
            ·
              refine ⟨128451055515270445799946713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85634037010180297199964475 128451055515270445799946713)
              ·
                refine ⟨96338291636452834349960035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128451055515270445799946713 96338291636452834349960035)
                ·
                  refine ⟨144507437454679251524940053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96338291636452834349960035 144507437454679251524940053)
                  ·
                    refine ⟨6773786130688089915231565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 144507437454679251524940053 6773786130688089915231565)
                    ·
                      refine ⟨2540169799008033718211837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6773786130688089915231565 2540169799008033718211837)
                      ·
                        rfl

theorem cell23_4946963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 3].length) (baseStart_4946963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946963 prefixEnd_4946963 := by exact prefixLift 4946963
  have htrace : WordTrace (prefixWord ++ tailWord_4946963) baseStart_4946963 baseEnd_4946963 := by
    simpa [prefixWord, tailWord_4946963, baseEnd_4946963] using wordTrace_append hprefix tailTrace_4946963
  have hstable : (prefixWord ++ tailWord_4946963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946963).length < 2 ^ (prefixWord ++ tailWord_4946963).sum := by decide
  have hdescent : baseEnd_4946963 < baseStart_4946963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946990 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_4946990 : Nat := 118140960795 + 4946990 * 2 ^ 59
def prefixEnd_4946990 : Nat := 4983230072969 + 3 ^ 40 * 4946990 * 2
def baseEnd_4946990 : Nat := 2540183662985705112574213

theorem tailTrace_4946990 : CollatzResearch.WordTrace tailWord_4946990 prefixEnd_4946990 2540183662985705112574213 := by
  unfold tailWord_4946990
  simp only [CollatzResearch.WordTrace]
  refine ⟨22553943543488447934110803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120287698898605055648590949 22553943543488447934110803)
  ·
    refine ⟨33830915315232671901166205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22553943543488447934110803 33830915315232671901166205)
    ·
      refine ⟨12686593243212251962937327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33830915315232671901166205 12686593243212251962937327)
      ·
        refine ⟨19029889864818377944405991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12686593243212251962937327 19029889864818377944405991)
        ·
          refine ⟨28544834797227566916608987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19029889864818377944405991 28544834797227566916608987)
          ·
            refine ⟨42817252195841350374913481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28544834797227566916608987 42817252195841350374913481)
            ·
              refine ⟨32112939146881012781185111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42817252195841350374913481 32112939146881012781185111)
              ·
                refine ⟨48169408720321519171777667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32112939146881012781185111 48169408720321519171777667)
                ·
                  refine ⟨72254113080482278757666501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48169408720321519171777667 72254113080482278757666501)
                  ·
                    refine ⟨13547646202590427267062469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72254113080482278757666501 13547646202590427267062469)
                    ·
                      refine ⟨2540183662985705112574213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13547646202590427267062469 2540183662985705112574213)
                      ·
                        rfl

theorem cell23_4946990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_4946990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946990 prefixEnd_4946990 := by exact prefixLift 4946990
  have htrace : WordTrace (prefixWord ++ tailWord_4946990) baseStart_4946990 baseEnd_4946990 := by
    simpa [prefixWord, tailWord_4946990, baseEnd_4946990] using wordTrace_append hprefix tailTrace_4946990
  have hstable : (prefixWord ++ tailWord_4946990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946990).length < 2 ^ (prefixWord ++ tailWord_4946990).sum := by decide
  have hdescent : baseEnd_4946990 < baseStart_4946990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4946994 : List Nat := [3, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2]
def baseStart_4946994 : Nat := 118140960795 + 4946994 * 2 ^ 59
def prefixEnd_4946994 : Nat := 4983230072969 + 3 ^ 40 * 4946994 * 2
def baseEnd_4946994 : Nat := 2540185716908323096924195

theorem tailTrace_4946994 : CollatzResearch.WordTrace tailWord_4946994 prefixEnd_4946994 2540185716908323096924195 := by
  unfold tailWord_4946994
  simp only [CollatzResearch.WordTrace]
  refine ⟨45107923559973273039008009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120287796159928728104021357 45107923559973273039008009)
  ·
    refine ⟨33830942669979954779256007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45107923559973273039008009 33830942669979954779256007)
    ·
      refine ⟨50746414004969932168884011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33830942669979954779256007 50746414004969932168884011)
      ·
        refine ⟨76119621007454898253326017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50746414004969932168884011 76119621007454898253326017)
        ·
          refine ⟨57089715755591173689994513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76119621007454898253326017 57089715755591173689994513)
          ·
            refine ⟨42817286816693380267495885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57089715755591173689994513 42817286816693380267495885)
            ·
              refine ⟨16056482556260017600310957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42817286816693380267495885 16056482556260017600310957)
              ·
                refine ⟨6021180958597506600116609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16056482556260017600310957 6021180958597506600116609)
                ·
                  refine ⟨4515885718948129950087457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6021180958597506600116609 4515885718948129950087457)
                  ·
                    refine ⟨3386914289211097462565593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4515885718948129950087457 3386914289211097462565593)
                    ·
                      refine ⟨2540185716908323096924195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3386914289211097462565593 2540185716908323096924195)
                      ·
                        rfl

theorem cell23_4946994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_4946994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4946994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4946994 prefixEnd_4946994 := by exact prefixLift 4946994
  have htrace : WordTrace (prefixWord ++ tailWord_4946994) baseStart_4946994 baseEnd_4946994 := by
    simpa [prefixWord, tailWord_4946994, baseEnd_4946994] using wordTrace_append hprefix tailTrace_4946994
  have hstable : (prefixWord ++ tailWord_4946994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4946994).length < 2 ^ (prefixWord ++ tailWord_4946994).sum := by decide
  have hdescent : baseEnd_4946994 < baseStart_4946994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4946994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947013 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 1, 7]
def baseStart_4947013 : Nat := 118140960795 + 4947013 * 2 ^ 59
def prefixEnd_4947013 : Nat := 4983230072969 + 3 ^ 40 * 4947013 * 2
def baseEnd_4947013 : Nat := 846731824346919507528869

theorem tailTrace_4947013 : CollatzResearch.WordTrace tailWord_4947013 prefixEnd_4947013 846731824346919507528869 := by
  unfold tailWord_4947013
  simp only [CollatzResearch.WordTrace]
  refine ⟨180432387226824258400973693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120288258151216172267315795 180432387226824258400973693)
  ·
    refine ⟨67662145210059096900365135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180432387226824258400973693 67662145210059096900365135)
    ·
      refine ⟨101493217815088645350547703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67662145210059096900365135 101493217815088645350547703)
      ·
        refine ⟨152239826722632968025821555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101493217815088645350547703 152239826722632968025821555)
        ·
          refine ⟨228359740083949452038732333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152239826722632968025821555 228359740083949452038732333)
          ·
            refine ⟨85634902531481044514524625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228359740083949452038732333 85634902531481044514524625)
            ·
              refine ⟨64226176898610783385893469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85634902531481044514524625 64226176898610783385893469)
              ·
                refine ⟨24084816336979043769710051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64226176898610783385893469 24084816336979043769710051)
                ·
                  refine ⟨36127224505468565654565077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24084816336979043769710051 36127224505468565654565077)
                  ·
                    refine ⟨846731824346919507528869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36127224505468565654565077 846731824346919507528869)
                    ·
                      rfl

theorem cell23_4947013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_4947013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947013 prefixEnd_4947013 := by exact prefixLift 4947013
  have htrace : WordTrace (prefixWord ++ tailWord_4947013) baseStart_4947013 baseEnd_4947013 := by
    simpa [prefixWord, tailWord_4947013, baseEnd_4947013] using wordTrace_append hprefix tailTrace_4947013
  have hstable : (prefixWord ++ tailWord_4947013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947013).length < 2 ^ (prefixWord ++ tailWord_4947013).sum := by decide
  have hdescent : baseEnd_4947013 < baseStart_4947013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947043 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 2, 8]
def baseStart_4947043 : Nat := 118140960795 + 4947043 * 2 ^ 59
def prefixEnd_4947043 : Nat := 4983230072969 + 3 ^ 40 * 4947043 * 2
def baseEnd_4947043 : Nat := 846736959153464468403823

theorem tailTrace_4947043 : CollatzResearch.WordTrace tailWord_4947043 prefixEnd_4947043 846736959153464468403823 := by
  unfold tailWord_4947043
  simp only [CollatzResearch.WordTrace]
  refine ⟨180433481416715573524565783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120288987611143715683043855 180433481416715573524565783)
  ·
    refine ⟨270650222125073360286848675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180433481416715573524565783 270650222125073360286848675)
    ·
      refine ⟨405975333187610040430273013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270650222125073360286848675 405975333187610040430273013)
      ·
        refine ⟨38060187486338441290338095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 405975333187610040430273013 38060187486338441290338095)
        ·
          refine ⟨57090281229507661935507143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38060187486338441290338095 57090281229507661935507143)
          ·
            refine ⟨85635421844261492903260715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57090281229507661935507143 85635421844261492903260715)
            ·
              refine ⟨128453132766392239354891073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85635421844261492903260715 128453132766392239354891073)
              ·
                refine ⟨96339849574794179516168305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128453132766392239354891073 96339849574794179516168305)
                ·
                  refine ⟨72254887181095634637126229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96339849574794179516168305 72254887181095634637126229)
                  ·
                    refine ⟨846736959153464468403823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72254887181095634637126229 846736959153464468403823)
                    ·
                      rfl

theorem cell23_4947043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 8].length) (baseStart_4947043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947043 prefixEnd_4947043 := by exact prefixLift 4947043
  have htrace : WordTrace (prefixWord ++ tailWord_4947043) baseStart_4947043 baseEnd_4947043 := by
    simpa [prefixWord, tailWord_4947043, baseEnd_4947043] using wordTrace_append hprefix tailTrace_4947043
  have hstable : (prefixWord ++ tailWord_4947043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947043).length < 2 ^ (prefixWord ++ tailWord_4947043).sum := by decide
  have hdescent : baseEnd_4947043 < baseStart_4947043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947127 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 1, 5, 2]
def baseStart_4947127 : Nat := 118140960795 + 4947127 * 2 ^ 59
def prefixEnd_4947127 : Nat := 4983230072969 + 3 ^ 40 * 4947127 * 2
def baseEnd_4947127 : Nat := 2540254009835371076561083

theorem tailTrace_4947127 : CollatzResearch.WordTrace tailWord_4947127 prefixEnd_4947127 2540254009835371076561083 := by
  unfold tailWord_4947127
  simp only [CollatzResearch.WordTrace]
  refine ⟨180436545148411255870623635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120291030098940837247082423 180436545148411255870623635)
  ·
    refine ⟨270654817722616883805935453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180436545148411255870623635 270654817722616883805935453)
    ·
      refine ⟨101495556645981331427225795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270654817722616883805935453 101495556645981331427225795)
      ·
        refine ⟨152243334968971997140838693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101495556645981331427225795 152243334968971997140838693)
        ·
          refine ⟨28545625306682249463907255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152243334968971997140838693 28545625306682249463907255)
          ·
            refine ⟨42818437960023374195860883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28545625306682249463907255 42818437960023374195860883)
            ·
              refine ⟨64227656940035061293791325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42818437960023374195860883 64227656940035061293791325)
              ·
                refine ⟨24085371352513147985171747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64227656940035061293791325 24085371352513147985171747)
                ·
                  refine ⟨36128057028769721977757621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24085371352513147985171747 36128057028769721977757621)
                  ·
                    refine ⟨3387005346447161435414777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36128057028769721977757621 3387005346447161435414777)
                    ·
                      refine ⟨2540254009835371076561083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3387005346447161435414777 2540254009835371076561083)
                      ·
                        rfl

theorem cell23_4947127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 5, 2].length) (baseStart_4947127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947127 prefixEnd_4947127 := by exact prefixLift 4947127
  have htrace : WordTrace (prefixWord ++ tailWord_4947127) baseStart_4947127 baseEnd_4947127 := by
    simpa [prefixWord, tailWord_4947127, baseEnd_4947127] using wordTrace_append hprefix tailTrace_4947127
  have hstable : (prefixWord ++ tailWord_4947127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947127).length < 2 ^ (prefixWord ++ tailWord_4947127).sum := by decide
  have hdescent : baseEnd_4947127 < baseStart_4947127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947138 : List Nat := [3, 5, 1, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_4947138 : Nat := 118140960795 + 4947138 * 2 ^ 59
def prefixEnd_4947138 : Nat := 4983230072969 + 3 ^ 40 * 4947138 * 2
def baseEnd_4947138 : Nat := 2540259658122570533523533

theorem tailTrace_4947138 : CollatzResearch.WordTrace tailWord_4947138 prefixEnd_4947138 2540259658122570533523533 := by
  unfold tailWord_4947138
  simp only [CollatzResearch.WordTrace]
  refine ⟨45109236587842851187318517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120291297567580936499516045 45109236587842851187318517)
  ·
    refine ⟨4228990930110267298811111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45109236587842851187318517 4228990930110267298811111)
    ·
      refine ⟨6343486395165400948216667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4228990930110267298811111 6343486395165400948216667)
      ·
        refine ⟨9515229592748101422325001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6343486395165400948216667 9515229592748101422325001)
        ·
          refine ⟨7136422194561076066743751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9515229592748101422325001 7136422194561076066743751)
          ·
            refine ⟨10704633291841614100115627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7136422194561076066743751 10704633291841614100115627)
            ·
              refine ⟨16056949937762421150173441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10704633291841614100115627 16056949937762421150173441)
              ·
                refine ⟨12042712453321815862630081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16056949937762421150173441 12042712453321815862630081)
                ·
                  refine ⟨9032034339991361896972561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12042712453321815862630081 9032034339991361896972561)
                  ·
                    refine ⟨6774025754993521422729421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9032034339991361896972561 6774025754993521422729421)
                    ·
                      refine ⟨2540259658122570533523533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6774025754993521422729421 2540259658122570533523533)
                      ·
                        rfl

theorem cell23_4947138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_4947138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947138 prefixEnd_4947138 := by exact prefixLift 4947138
  have htrace : WordTrace (prefixWord ++ tailWord_4947138) baseStart_4947138 baseEnd_4947138 := by
    simpa [prefixWord, tailWord_4947138, baseEnd_4947138] using wordTrace_append hprefix tailTrace_4947138
  have hstable : (prefixWord ++ tailWord_4947138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947138).length < 2 ^ (prefixWord ++ tailWord_4947138).sum := by decide
  have hdescent : baseEnd_4947138 < baseStart_4947138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947158 : List Nat := [5, 2, 1, 2, 2, 2, 2, 1, 6]
def baseStart_4947158 : Nat := 118140960795 + 4947158 * 2 ^ 59
def prefixEnd_4947158 : Nat := 4983230072969 + 3 ^ 40 * 4947158 * 2
def baseEnd_4947158 : Nat := 282252214192851161697049

theorem tailTrace_4947158 : CollatzResearch.WordTrace tailWord_4947158 prefixEnd_4947158 282252214192851161697049 := by
  unfold tailWord_4947158
  simp only [CollatzResearch.WordTrace]
  refine ⟨11277354738206184260312633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120291783874199298776668085 11277354738206184260312633)
  ·
    refine ⟨8458016053654638195234475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11277354738206184260312633 8458016053654638195234475)
    ·
      refine ⟨12687024080481957292851713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8458016053654638195234475 12687024080481957292851713)
      ·
        refine ⟨9515268060361467969638785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12687024080481957292851713 9515268060361467969638785)
        ·
          refine ⟨7136451045271100977229089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9515268060361467969638785 7136451045271100977229089)
          ·
            refine ⟨5352338283953325732921817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7136451045271100977229089 5352338283953325732921817)
            ·
              refine ⟨4014253712964994299691363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5352338283953325732921817 4014253712964994299691363)
              ·
                refine ⟨6021380569447491449537045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4014253712964994299691363 6021380569447491449537045)
                ·
                  refine ⟨282252214192851161697049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6021380569447491449537045 282252214192851161697049)
                  ·
                    rfl

theorem cell23_4947158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_4947158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947158 prefixEnd_4947158 := by exact prefixLift 4947158
  have htrace : WordTrace (prefixWord ++ tailWord_4947158) baseStart_4947158 baseEnd_4947158 := by
    simpa [prefixWord, tailWord_4947158, baseEnd_4947158] using wordTrace_append hprefix tailTrace_4947158
  have hstable : (prefixWord ++ tailWord_4947158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947158).length < 2 ^ (prefixWord ++ tailWord_4947158).sum := by decide
  have hdescent : baseEnd_4947158 < baseStart_4947158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947180 : List Nat := [2, 2, 1, 1, 2, 4, 2, 9]
def baseStart_4947180 : Nat := 118140960795 + 4947180 * 2 ^ 59
def prefixEnd_4947180 : Nat := 4983230072969 + 3 ^ 40 * 4947180 * 2
def baseEnd_4947180 : Nat := 94084489789261458118457

theorem tailTrace_4947180 : CollatzResearch.WordTrace tailWord_4947180 prefixEnd_4947180 94084489789261458118457 := by
  unfold tailWord_4947180
  simp only [CollatzResearch.WordTrace]
  refine ⟨90219239108609622961151497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120292318811479497281535329 90219239108609622961151497)
  ·
    refine ⟨67664429331457217220863623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90219239108609622961151497 67664429331457217220863623)
    ·
      refine ⟨101496643997185825831295435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67664429331457217220863623 101496643997185825831295435)
      ·
        refine ⟨152244965995778738746943153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101496643997185825831295435 152244965995778738746943153)
        ·
          refine ⟨114183724496834054060207365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152244965995778738746943153 114183724496834054060207365)
          ·
            refine ⟨21409448343156385136288881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114183724496834054060207365 21409448343156385136288881)
            ·
              refine ⟨16057086257367288852216661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21409448343156385136288881 16057086257367288852216661)
              ·
                refine ⟨94084489789261458118457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16057086257367288852216661 94084489789261458118457)
                ·
                  rfl

theorem cell23_4947180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 9].length) (baseStart_4947180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947180 prefixEnd_4947180 := by exact prefixLift 4947180
  have htrace : WordTrace (prefixWord ++ tailWord_4947180) baseStart_4947180 baseEnd_4947180 := by
    simpa [prefixWord, tailWord_4947180, baseEnd_4947180] using wordTrace_append hprefix tailTrace_4947180
  have hstable : (prefixWord ++ tailWord_4947180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947180).length < 2 ^ (prefixWord ++ tailWord_4947180).sum := by decide
  have hdescent : baseEnd_4947180 < baseStart_4947180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947187 : List Nat := [1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 4]
def baseStart_4947187 : Nat := 118140960795 + 4947187 * 2 ^ 59
def prefixEnd_4947187 : Nat := 4983230072969 + 3 ^ 40 * 4947187 * 2
def baseEnd_4947187 : Nat := 2540284818674640841810807

theorem tailTrace_4947187 : CollatzResearch.WordTrace tailWord_4947187 prefixEnd_4947187 2540284818674640841810807 := by
  unfold tailWord_4947187
  simp only [CollatzResearch.WordTrace]
  refine ⟨180438733528193886117807815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120292489018795924078538543 180438733528193886117807815)
  ·
    refine ⟨270658100292290829176711723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180438733528193886117807815 270658100292290829176711723)
    ·
      refine ⟨405987150438436243765067585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270658100292290829176711723 405987150438436243765067585)
      ·
        refine ⟨304490362828827182823800689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 405987150438436243765067585 304490362828827182823800689)
        ·
          refine ⟨228367772121620387117850517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304490362828827182823800689 228367772121620387117850517)
          ·
            refine ⟨10704739318200955646149243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 228367772121620387117850517 10704739318200955646149243)
            ·
              refine ⟨16057108977301433469223865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10704739318200955646149243 16057108977301433469223865)
              ·
                refine ⟨12042831732976075101917899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16057108977301433469223865 12042831732976075101917899)
                ·
                  refine ⟨18064247599464112652876849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12042831732976075101917899 18064247599464112652876849)
                  ·
                    refine ⟨13548185699598084489657637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18064247599464112652876849 13548185699598084489657637)
                    ·
                      refine ⟨2540284818674640841810807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13548185699598084489657637 2540284818674640841810807)
                      ·
                        rfl

theorem cell23_4947187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 4].length) (baseStart_4947187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947187 prefixEnd_4947187 := by exact prefixLift 4947187
  have htrace : WordTrace (prefixWord ++ tailWord_4947187) baseStart_4947187 baseEnd_4947187 := by
    simpa [prefixWord, tailWord_4947187, baseEnd_4947187] using wordTrace_append hprefix tailTrace_4947187
  have hstable : (prefixWord ++ tailWord_4947187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947187).length < 2 ^ (prefixWord ++ tailWord_4947187).sum := by decide
  have hdescent : baseEnd_4947187 < baseStart_4947187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947202 : List Nat := [3, 4, 1, 1, 3, 2, 2, 2, 1, 1, 3]
def baseStart_4947202 : Nat := 118140960795 + 4947202 * 2 ^ 59
def prefixEnd_4947202 : Nat := 4983230072969 + 3 ^ 40 * 4947202 * 2
def baseEnd_4947202 : Nat := 2540292520884458283123239

theorem tailTrace_4947202 : CollatzResearch.WordTrace tailWord_4947202 prefixEnd_4947202 2540292520884458283123239 := by
  unfold tailWord_4947202
  simp only [CollatzResearch.WordTrace]
  refine ⟨45109820155784885919900965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120292853748759695786402573 45109820155784885919900965)
  ·
    refine ⟨8458091279209666109981431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45109820155784885919900965 8458091279209666109981431)
    ·
      refine ⟨12687136918814499164972147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8458091279209666109981431 12687136918814499164972147)
      ·
        refine ⟨19030705378221748747458221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12687136918814499164972147 19030705378221748747458221)
        ·
          refine ⟨7136514516833155780296833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19030705378221748747458221 7136514516833155780296833)
          ·
            refine ⟨5352385887624866835222625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7136514516833155780296833 5352385887624866835222625)
            ·
              refine ⟨4014289415718650126416969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5352385887624866835222625 4014289415718650126416969)
              ·
                refine ⟨3010717061788987594812727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4014289415718650126416969 3010717061788987594812727)
                ·
                  refine ⟨4516075592683481392219091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3010717061788987594812727 4516075592683481392219091)
                  ·
                    refine ⟨6774113389025222088328637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4516075592683481392219091 6774113389025222088328637)
                    ·
                      refine ⟨2540292520884458283123239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6774113389025222088328637 2540292520884458283123239)
                      ·
                        rfl

theorem cell23_4947202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_4947202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947202 prefixEnd_4947202 := by exact prefixLift 4947202
  have htrace : WordTrace (prefixWord ++ tailWord_4947202) baseStart_4947202 baseEnd_4947202 := by
    simpa [prefixWord, tailWord_4947202, baseEnd_4947202] using wordTrace_append hprefix tailTrace_4947202
  have hstable : (prefixWord ++ tailWord_4947202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947202).length < 2 ^ (prefixWord ++ tailWord_4947202).sum := by decide
  have hdescent : baseEnd_4947202 < baseStart_4947202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947224 : List Nat := [2, 1, 2, 3, 1, 4, 2, 1, 1, 3, 3]
def baseStart_4947224 : Nat := 118140960795 + 4947224 * 2 ^ 59
def prefixEnd_4947224 : Nat := 4983230072969 + 3 ^ 40 * 4947224 * 2
def baseEnd_4947224 : Nat := 2540303817458857197048137

theorem tailTrace_4947224 : CollatzResearch.WordTrace tailWord_4947224 prefixEnd_4947224 2540303817458857197048137 := by
  unfold tailWord_4947224
  simp only [CollatzResearch.WordTrace]
  refine ⟨90220041514529920718452363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120293388686039894291269817 90220041514529920718452363)
  ·
    refine ⟨135330062271794881077678545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90220041514529920718452363 135330062271794881077678545)
    ·
      refine ⟨101497546703846160808258909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135330062271794881077678545 101497546703846160808258909)
      ·
        refine ⟨38061580013942310303097091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101497546703846160808258909 38061580013942310303097091)
        ·
          refine ⟨57092370020913465454645637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38061580013942310303097091 57092370020913465454645637)
          ·
            refine ⟨10704819378921274772746057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57092370020913465454645637 10704819378921274772746057)
            ·
              refine ⟨8028614534190956079559543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10704819378921274772746057 8028614534190956079559543)
              ·
                refine ⟨12042921801286434119339315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8028614534190956079559543 12042921801286434119339315)
                ·
                  refine ⟨18064382701929651179008973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12042921801286434119339315 18064382701929651179008973)
                  ·
                    refine ⟨6774143513223619192128365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18064382701929651179008973 6774143513223619192128365)
                    ·
                      refine ⟨2540303817458857197048137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6774143513223619192128365 2540303817458857197048137)
                      ·
                        rfl

theorem cell23_4947224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_4947224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947224 prefixEnd_4947224 := by exact prefixLift 4947224
  have htrace : WordTrace (prefixWord ++ tailWord_4947224) baseStart_4947224 baseEnd_4947224 := by
    simpa [prefixWord, tailWord_4947224, baseEnd_4947224] using wordTrace_append hprefix tailTrace_4947224
  have hstable : (prefixWord ++ tailWord_4947224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947224).length < 2 ^ (prefixWord ++ tailWord_4947224).sum := by decide
  have hdescent : baseEnd_4947224 < baseStart_4947224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947245 : List Nat := [1, 5, 3, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_4947245 : Nat := 118140960795 + 4947245 * 2 ^ 59
def prefixEnd_4947245 : Nat := 4983230072969 + 3 ^ 40 * 4947245 * 2
def baseEnd_4947245 : Nat := 2540314600552601614885541

theorem tailTrace_4947245 : CollatzResearch.WordTrace tailWord_4947245 prefixEnd_4947245 2540314600552601614885541 := by
  unfold tailWord_4947245
  simp only [CollatzResearch.WordTrace]
  refine ⟨180440848961983762023419189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120293899307989174682279459 180440848961983762023419189)
  ·
    refine ⟨16916329590185977689695549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 180440848961983762023419189 16916329590185977689695549)
    ·
      refine ⟨6343623596319741633635831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16916329590185977689695549 6343623596319741633635831)
      ·
        refine ⟨9515435394479612450453747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6343623596319741633635831 9515435394479612450453747)
        ·
          refine ⟨14273153091719418675680621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9515435394479612450453747 14273153091719418675680621)
          ·
            refine ⟨5352432409394782003380233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14273153091719418675680621 5352432409394782003380233)
            ·
              refine ⟨4014324307046086502535175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5352432409394782003380233 4014324307046086502535175)
              ·
                refine ⟨6021486460569129753802763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4014324307046086502535175 6021486460569129753802763)
                ·
                  refine ⟨9032229690853694630704145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6021486460569129753802763 9032229690853694630704145)
                  ·
                    refine ⟨6774172268140270973028109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9032229690853694630704145 6774172268140270973028109)
                    ·
                      refine ⟨2540314600552601614885541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6774172268140270973028109 2540314600552601614885541)
                      ·
                        rfl

theorem cell23_4947245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_4947245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947245 prefixEnd_4947245 := by exact prefixLift 4947245
  have htrace : WordTrace (prefixWord ++ tailWord_4947245) baseStart_4947245 baseEnd_4947245 := by
    simpa [prefixWord, tailWord_4947245, baseEnd_4947245] using wordTrace_append hprefix tailTrace_4947245
  have hstable : (prefixWord ++ tailWord_4947245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947245).length < 2 ^ (prefixWord ++ tailWord_4947245).sum := by decide
  have hdescent : baseEnd_4947245 < baseStart_4947245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947251 : List Nat := [1, 1, 1, 2, 5, 3, 1, 3, 1, 3, 2]
def baseStart_4947251 : Nat := 118140960795 + 4947251 * 2 ^ 59
def prefixEnd_4947251 : Nat := 4983230072969 + 3 ^ 40 * 4947251 * 2
def baseEnd_4947251 : Nat := 2540317681436528591410513

theorem tailTrace_4947251 : CollatzResearch.WordTrace tailWord_4947251 prefixEnd_4947251 2540317681436528591410513 := by
  unfold tailWord_4947251
  simp only [CollatzResearch.WordTrace]
  refine ⟨180441067799962025048137607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120294045199974683365425071 180441067799962025048137607)
  ·
    refine ⟨270661601699943037572206411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180441067799962025048137607 270661601699943037572206411)
    ·
      refine ⟨405992402549914556358309617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270661601699943037572206411 405992402549914556358309617)
      ·
        refine ⟨304494301912435917268732213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 405992402549914556358309617 304494301912435917268732213)
        ·
          refine ⟨28546340804290867243943645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 304494301912435917268732213 28546340804290867243943645)
          ·
            refine ⟨10704877801609075216478867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28546340804290867243943645 10704877801609075216478867)
            ·
              refine ⟨16057316702413612824718301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10704877801609075216478867 16057316702413612824718301)
              ·
                refine ⟨6021493763405104809269363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16057316702413612824718301 6021493763405104809269363)
                ·
                  refine ⟨9032240645107657213904045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6021493763405104809269363 9032240645107657213904045)
                  ·
                    refine ⟨3387090241915371455214017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9032240645107657213904045 3387090241915371455214017)
                    ·
                      refine ⟨2540317681436528591410513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3387090241915371455214017 2540317681436528591410513)
                      ·
                        rfl

theorem cell23_4947251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 3, 2].length) (baseStart_4947251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947251 prefixEnd_4947251 := by exact prefixLift 4947251
  have htrace : WordTrace (prefixWord ++ tailWord_4947251) baseStart_4947251 baseEnd_4947251 := by
    simpa [prefixWord, tailWord_4947251, baseEnd_4947251] using wordTrace_append hprefix tailTrace_4947251
  have hstable : (prefixWord ++ tailWord_4947251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947251).length < 2 ^ (prefixWord ++ tailWord_4947251).sum := by decide
  have hdescent : baseEnd_4947251 < baseStart_4947251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947287 : List Nat := [1, 1, 3, 2, 3, 2, 2, 2, 7]
def baseStart_4947287 : Nat := 118140960795 + 4947287 * 2 ^ 59
def prefixEnd_4947287 : Nat := 4983230072969 + 3 ^ 40 * 4947287 * 2
def baseEnd_4947287 : Nat := 282259574082232272284483

theorem tailTrace_4947287 : CollatzResearch.WordTrace tailWord_4947287 prefixEnd_4947287 282259574082232272284483 := by
  unfold tailWord_4947287
  simp only [CollatzResearch.WordTrace]
  refine ⟨180442380827831603196448115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120294920551887735464298743 180442380827831603196448115)
  ·
    refine ⟨270663571241747404794672173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180442380827831603196448115 270663571241747404794672173)
    ·
      refine ⟨101498839215655276798002065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270663571241747404794672173 101498839215655276798002065)
      ·
        refine ⟨76124129411741457598501549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101498839215655276798002065 76124129411741457598501549)
        ·
          refine ⟨28546548529403046599438081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76124129411741457598501549 28546548529403046599438081)
          ·
            refine ⟨21409911397052284949578561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28546548529403046599438081 21409911397052284949578561)
            ·
              refine ⟨16057433547789213712183921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21409911397052284949578561 16057433547789213712183921)
              ·
                refine ⟨12043075160841910284137941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16057433547789213712183921 12043075160841910284137941)
                ·
                  refine ⟨282259574082232272284483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12043075160841910284137941 282259574082232272284483)
                  ·
                    rfl

theorem cell23_4947287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 7].length) (baseStart_4947287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947287 prefixEnd_4947287 := by exact prefixLift 4947287
  have htrace : WordTrace (prefixWord ++ tailWord_4947287) baseStart_4947287 baseEnd_4947287 := by
    simpa [prefixWord, tailWord_4947287, baseEnd_4947287] using wordTrace_append hprefix tailTrace_4947287
  have hstable : (prefixWord ++ tailWord_4947287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947287).length < 2 ^ (prefixWord ++ tailWord_4947287).sum := by decide
  have hdescent : baseEnd_4947287 < baseStart_4947287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947297 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 1, 5, 3]
def baseStart_4947297 : Nat := 118140960795 + 4947297 * 2 ^ 59
def prefixEnd_4947297 : Nat := 4983230072969 + 3 ^ 40 * 4947297 * 2
def baseEnd_4947297 : Nat := 2540341301546635411435301

theorem tailTrace_4947297 : CollatzResearch.WordTrace tailWord_4947297 prefixEnd_4947297 2540341301546635411435301 := by
  unfold tailWord_4947297
  simp only [CollatzResearch.WordTrace]
  refine ⟨180442745557795374904312145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120295163705196916602874763 180442745557795374904312145)
  ·
    refine ⟨135332059168346531178234109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180442745557795374904312145 135332059168346531178234109)
    ·
      refine ⟨50749522188129949191837791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135332059168346531178234109 50749522188129949191837791)
      ·
        refine ⟨76124283282194923787756687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50749522188129949191837791 76124283282194923787756687)
        ·
          refine ⟨114186424923292385681635031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76124283282194923787756687 114186424923292385681635031)
          ·
            refine ⟨171279637384938578522452547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114186424923292385681635031 171279637384938578522452547)
            ·
              refine ⟨256919456077407867783678821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171279637384938578522452547 256919456077407867783678821)
              ·
                refine ⟨48172398014513975209439779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 256919456077407867783678821 48172398014513975209439779)
                ·
                  refine ⟨72258597021770962814159669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48172398014513975209439779 72258597021770962814159669)
                  ·
                    refine ⟨6774243470791027763827469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72258597021770962814159669 6774243470791027763827469)
                    ·
                      refine ⟨2540341301546635411435301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6774243470791027763827469 2540341301546635411435301)
                      ·
                        rfl

theorem cell23_4947297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_4947297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947297 prefixEnd_4947297 := by exact prefixLift 4947297
  have htrace : WordTrace (prefixWord ++ tailWord_4947297) baseStart_4947297 baseEnd_4947297 := by
    simpa [prefixWord, tailWord_4947297, baseEnd_4947297] using wordTrace_append hprefix tailTrace_4947297
  have hstable : (prefixWord ++ tailWord_4947297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947297).length < 2 ^ (prefixWord ++ tailWord_4947297).sum := by decide
  have hdescent : baseEnd_4947297 < baseStart_4947297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947324 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 2, 5, 2]
def baseStart_4947324 : Nat := 118140960795 + 4947324 * 2 ^ 59
def prefixEnd_4947324 : Nat := 4983230072969 + 3 ^ 40 * 4947324 * 2
def baseEnd_4947324 : Nat := 2540355165524306805797677

theorem tailTrace_4947324 : CollatzResearch.WordTrace tailWord_4947324 prefixEnd_4947324 2540355165524306805797677 := by
  unfold tailWord_4947324
  simp only [CollatzResearch.WordTrace]
  refine ⟨90221865164348779257772513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120295820219131705677030017 90221865164348779257772513)
  ·
    refine ⟨67666398873261584443329385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90221865164348779257772513 67666398873261584443329385)
    ·
      refine ⟨50749799154946188332497039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67666398873261584443329385 50749799154946188332497039)
      ·
        refine ⟨76124698732419282498745559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50749799154946188332497039 76124698732419282498745559)
        ·
          refine ⟨114187048098628923748118339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76124698732419282498745559 114187048098628923748118339)
          ·
            refine ⟨171280572147943385622177509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114187048098628923748118339 171280572147943385622177509)
            ·
              refine ⟨32115107277739384804158283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171280572147943385622177509 32115107277739384804158283)
              ·
                refine ⟨48172660916609077206237425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32115107277739384804158283 48172660916609077206237425)
                ·
                  refine ⟨36129495687456807904678069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48172660916609077206237425 36129495687456807904678069)
                  ·
                    refine ⟨3387140220699075741063569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36129495687456807904678069 3387140220699075741063569)
                    ·
                      refine ⟨2540355165524306805797677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3387140220699075741063569 2540355165524306805797677)
                      ·
                        rfl

theorem cell23_4947324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_4947324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947324 prefixEnd_4947324 := by exact prefixLift 4947324
  have htrace : WordTrace (prefixWord ++ tailWord_4947324) baseStart_4947324 baseEnd_4947324 := by
    simpa [prefixWord, tailWord_4947324, baseEnd_4947324] using wordTrace_append hprefix tailTrace_4947324
  have hstable : (prefixWord ++ tailWord_4947324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947324).length < 2 ^ (prefixWord ++ tailWord_4947324).sum := by decide
  have hdescent : baseEnd_4947324 < baseStart_4947324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947388 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 2, 4, 2]
def baseStart_4947388 : Nat := 118140960795 + 4947388 * 2 ^ 59
def prefixEnd_4947388 : Nat := 4983230072969 + 3 ^ 40 * 4947388 * 2
def baseEnd_4947388 : Nat := 2540388028286194555397383

theorem tailTrace_4947388 : CollatzResearch.WordTrace tailWord_4947388 prefixEnd_4947388 2540388028286194555397383 := by
  unfold tailWord_4947388
  simp only [CollatzResearch.WordTrace]
  refine ⟨90223032300232848722937409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120297376400310464963916545 90223032300232848722937409)
  ·
    refine ⟨67667274225174636542203057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90223032300232848722937409 67667274225174636542203057)
    ·
      refine ⟨50750455668880977406652293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67667274225174636542203057 50750455668880977406652293)
      ·
        refine ⟨9515710437915183263747305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50750455668880977406652293 9515710437915183263747305)
        ·
          refine ⟨7136782828436387447810479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9515710437915183263747305 7136782828436387447810479)
          ·
            refine ⟨10705174242654581171715719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7136782828436387447810479 10705174242654581171715719)
            ·
              refine ⟨16057761363981871757573579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10705174242654581171715719 16057761363981871757573579)
              ·
                refine ⟨24086642045972807636360369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16057761363981871757573579 24086642045972807636360369)
                ·
                  refine ⟨18064981534479605727270277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24086642045972807636360369 18064981534479605727270277)
                  ·
                    refine ⟨3387184037714926073863177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18064981534479605727270277 3387184037714926073863177)
                    ·
                      refine ⟨2540388028286194555397383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3387184037714926073863177 2540388028286194555397383)
                      ·
                        rfl

theorem cell23_4947388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_4947388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947388 prefixEnd_4947388 := by exact prefixLift 4947388
  have htrace : WordTrace (prefixWord ++ tailWord_4947388) baseStart_4947388 baseEnd_4947388 := by
    simpa [prefixWord, tailWord_4947388, baseEnd_4947388] using wordTrace_append hprefix tailTrace_4947388
  have hstable : (prefixWord ++ tailWord_4947388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947388).length < 2 ^ (prefixWord ++ tailWord_4947388).sum := by decide
  have hdescent : baseEnd_4947388 < baseStart_4947388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947438 : List Nat := [4, 1, 2, 1, 2, 1, 4, 1, 3, 1, 3]
def baseStart_4947438 : Nat := 118140960795 + 4947438 * 2 ^ 59
def prefixEnd_4947438 : Nat := 4983230072969 + 3 ^ 40 * 4947438 * 2
def baseEnd_4947438 : Nat := 2540413702318919359772153

theorem tailTrace_4947438 : CollatzResearch.WordTrace tailWord_4947438 prefixEnd_4947438 2540413702318919359772153 := by
  unfold tailWord_4947438
  simp only [CollatzResearch.WordTrace]
  refine ⟨22555986031285569498149371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120298592166856370656796645 22555986031285569498149371)
  ·
    refine ⟨33833979046928354247224057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22555986031285569498149371 33833979046928354247224057)
    ·
      refine ⟨25375484285196265685418043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33833979046928354247224057 25375484285196265685418043)
      ·
        refine ⟨38063226427794398528127065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25375484285196265685418043 38063226427794398528127065)
        ·
          refine ⟨28547419820845798896095299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38063226427794398528127065 28547419820845798896095299)
          ·
            refine ⟨42821129731268698344142949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28547419820845798896095299 42821129731268698344142949)
            ·
              refine ⟨8028961824612880939526803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42821129731268698344142949 8028961824612880939526803)
              ·
                refine ⟨12043442736919321409290205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8028961824612880939526803 12043442736919321409290205)
                ·
                  refine ⟨4516291026344745528483827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12043442736919321409290205 4516291026344745528483827)
                  ·
                    refine ⟨6774436539517118292725741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4516291026344745528483827 6774436539517118292725741)
                    ·
                      refine ⟨2540413702318919359772153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6774436539517118292725741 2540413702318919359772153)
                      ·
                        rfl

theorem cell23_4947438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_4947438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947438 prefixEnd_4947438 := by exact prefixLift 4947438
  have htrace : WordTrace (prefixWord ++ tailWord_4947438) baseStart_4947438 baseEnd_4947438 := by
    simpa [prefixWord, tailWord_4947438, baseEnd_4947438] using wordTrace_append hprefix tailTrace_4947438
  have hstable : (prefixWord ++ tailWord_4947438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947438).length < 2 ^ (prefixWord ++ tailWord_4947438).sum := by decide
  have hdescent : baseEnd_4947438 < baseStart_4947438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947458 : List Nat := [3, 4, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_4947458 : Nat := 118140960795 + 4947458 * 2 ^ 59
def prefixEnd_4947458 : Nat := 4983230072969 + 3 ^ 40 * 4947458 * 2
def baseEnd_4947458 : Nat := 846807990644003093840687

theorem tailTrace_4947458 : CollatzResearch.WordTrace tailWord_4947458 prefixEnd_4947458 846807990644003093840687 := by
  unfold tailWord_4947458
  simp only [CollatzResearch.WordTrace]
  refine ⟨45112154427553024850230757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120299078473474732933948685 45112154427553024850230757)
  ·
    refine ⟨8458528955166192159418267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45112154427553024850230757 8458528955166192159418267)
    ·
      refine ⟨12687793432749288239127401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8458528955166192159418267 12687793432749288239127401)
      ·
        refine ⟨9515845074561966179345551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12687793432749288239127401 9515845074561966179345551)
        ·
          refine ⟨14273767611842949269018327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9515845074561966179345551 14273767611842949269018327)
          ·
            refine ⟨21410651417764423903527491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14273767611842949269018327 21410651417764423903527491)
            ·
              refine ⟨32115977126646635855291237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21410651417764423903527491 32115977126646635855291237)
              ·
                refine ⟨6021745711246244222867107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32115977126646635855291237 6021745711246244222867107)
                ·
                  refine ⟨9032618566869366334300661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6021745711246244222867107 9032618566869366334300661)
                  ·
                    refine ⟨846807990644003093840687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9032618566869366334300661 846807990644003093840687)
                    ·
                      rfl

theorem cell23_4947458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_4947458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947458 prefixEnd_4947458 := by exact prefixLift 4947458
  have htrace : WordTrace (prefixWord ++ tailWord_4947458) baseStart_4947458 baseEnd_4947458 := by
    simpa [prefixWord, tailWord_4947458, baseEnd_4947458] using wordTrace_append hprefix tailTrace_4947458
  have hstable : (prefixWord ++ tailWord_4947458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947458).length < 2 ^ (prefixWord ++ tailWord_4947458).sum := by decide
  have hdescent : baseEnd_4947458 < baseStart_4947458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947544 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 2, 6]
def baseStart_4947544 : Nat := 118140960795 + 4947544 * 2 ^ 59
def prefixEnd_4947544 : Nat := 4983230072969 + 3 ^ 40 * 4947544 * 2
def baseEnd_4947544 : Nat := 846822710422765315015555

theorem tailTrace_4947544 : CollatzResearch.WordTrace tailWord_4947544 prefixEnd_4947544 846822710422765315015555 := by
  unfold tailWord_4947544
  simp only [CollatzResearch.WordTrace]
  refine ⟨90225877193950268044276843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120301169591933690725702457 90225877193950268044276843)
  ·
    refine ⟨135338815790925402066415265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90225877193950268044276843 135338815790925402066415265)
    ·
      refine ⟨101504111843194051549811449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135338815790925402066415265 101504111843194051549811449)
      ·
        refine ⟨76128083882395538662358587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101504111843194051549811449 76128083882395538662358587)
        ·
          refine ⟨114192125823593307993537881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76128083882395538662358587 114192125823593307993537881)
          ·
            refine ⟨85644094367694980995153411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114192125823593307993537881 85644094367694980995153411)
            ·
              refine ⟨128466141551542471492730117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85644094367694980995153411 128466141551542471492730117)
              ·
                refine ⟨24087401540914213404886897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128466141551542471492730117 24087401540914213404886897)
                ·
                  refine ⟨18065551155685660053665173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24087401540914213404886897 18065551155685660053665173)
                  ·
                    refine ⟨846822710422765315015555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18065551155685660053665173 846822710422765315015555)
                    ·
                      rfl

theorem cell23_4947544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_4947544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947544 prefixEnd_4947544 := by exact prefixLift 4947544
  have htrace : WordTrace (prefixWord ++ tailWord_4947544) baseStart_4947544 baseEnd_4947544 := by
    simpa [prefixWord, tailWord_4947544, baseEnd_4947544] using wordTrace_append hprefix tailTrace_4947544
  have hstable : (prefixWord ++ tailWord_4947544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947544).length < 2 ^ (prefixWord ++ tailWord_4947544).sum := by decide
  have hdescent : baseEnd_4947544 < baseStart_4947544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947568 : List Nat := [2, 1, 1, 1, 6, 1, 1, 3, 1, 4, 2]
def baseStart_4947568 : Nat := 118140960795 + 4947568 * 2 ^ 59
def prefixEnd_4947568 : Nat := 4983230072969 + 3 ^ 40 * 4947568 * 2
def baseEnd_4947568 : Nat := 2540480454804003851146555

theorem tailTrace_4947568 : CollatzResearch.WordTrace tailWord_4947568 prefixEnd_4947568 2540480454804003851146555 := by
  unfold tailWord_4947568
  simp only [CollatzResearch.WordTrace]
  refine ⟨90226314869906794093713679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120301753159875725458284905 90226314869906794093713679)
  ·
    refine ⟨135339472304860191140570519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90226314869906794093713679 135339472304860191140570519)
    ·
      refine ⟨203009208457290286710855779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135339472304860191140570519 203009208457290286710855779)
      ·
        refine ⟨304513812685935430066283669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203009208457290286710855779 304513812685935430066283669)
        ·
          refine ⟨14274084969653223284357047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 304513812685935430066283669 14274084969653223284357047)
          ·
            refine ⟨21411127454479834926535571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14274084969653223284357047 21411127454479834926535571)
            ·
              refine ⟨32116691181719752389803357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21411127454479834926535571 32116691181719752389803357)
              ·
                refine ⟨12043759193144907146176259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32116691181719752389803357 12043759193144907146176259)
                ·
                  refine ⟨18065638789717360719264389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12043759193144907146176259 18065638789717360719264389)
                  ·
                    refine ⟨3387307273072005134862073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18065638789717360719264389 3387307273072005134862073)
                    ·
                      refine ⟨2540480454804003851146555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3387307273072005134862073 2540480454804003851146555)
                      ·
                        rfl

theorem cell23_4947568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 1, 4, 2].length) (baseStart_4947568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947568 prefixEnd_4947568 := by exact prefixLift 4947568
  have htrace : WordTrace (prefixWord ++ tailWord_4947568) baseStart_4947568 baseEnd_4947568 := by
    simpa [prefixWord, tailWord_4947568, baseEnd_4947568] using wordTrace_append hprefix tailTrace_4947568
  have hstable : (prefixWord ++ tailWord_4947568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947568).length < 2 ^ (prefixWord ++ tailWord_4947568).sum := by decide
  have hdescent : baseEnd_4947568 < baseStart_4947568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947602 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_4947602 : Nat := 118140960795 + 4947602 * 2 ^ 59
def prefixEnd_4947602 : Nat := 4983230072969 + 3 ^ 40 * 4947602 * 2
def baseEnd_4947602 : Nat := 2540497913146256718121399

theorem tailTrace_4947602 : CollatzResearch.WordTrace tailWord_4947602 prefixEnd_4947602 2540497913146256718121399 := by
  unfold tailWord_4947602
  simp only [CollatzResearch.WordTrace]
  refine ⟨45113467455422602998541265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120302579881126941329443373 45113467455422602998541265)
  ·
    refine ⟨33835100591566952248905949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45113467455422602998541265 33835100591566952248905949)
    ·
      refine ⟨12688162721837607093339731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33835100591566952248905949 12688162721837607093339731)
      ·
        refine ⟨19032244082756410640009597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12688162721837607093339731 19032244082756410640009597)
        ·
          refine ⟨7137091531033653990003599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19032244082756410640009597 7137091531033653990003599)
          ·
            refine ⟨10705637296550480985005399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7137091531033653990003599 10705637296550480985005399)
            ·
              refine ⟨16058455944825721477508099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10705637296550480985005399 16058455944825721477508099)
              ·
                refine ⟨24087683917238582216262149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16058455944825721477508099 24087683917238582216262149)
                ·
                  refine ⟨4516440734482234165549153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24087683917238582216262149 4516440734482234165549153)
                  ·
                    refine ⟨3387330550861675624161865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4516440734482234165549153 3387330550861675624161865)
                    ·
                      refine ⟨2540497913146256718121399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3387330550861675624161865 2540497913146256718121399)
                      ·
                        rfl

theorem cell23_4947602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_4947602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947602 prefixEnd_4947602 := by exact prefixLift 4947602
  have htrace : WordTrace (prefixWord ++ tailWord_4947602) baseStart_4947602 baseEnd_4947602 := by
    simpa [prefixWord, tailWord_4947602, baseEnd_4947602] using wordTrace_append hprefix tailTrace_4947602
  have hstable : (prefixWord ++ tailWord_4947602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947602).length < 2 ^ (prefixWord ++ tailWord_4947602).sum := by decide
  have hdescent : baseEnd_4947602 < baseStart_4947602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947608 : List Nat := [2, 1, 2, 4, 1, 2, 2, 4, 5]
def baseStart_4947608 : Nat := 118140960795 + 4947608 * 2 ^ 59
def prefixEnd_4947608 : Nat := 4983230072969 + 3 ^ 40 * 4947608 * 2
def baseEnd_4947608 : Nat := 282277888225575966071819

theorem tailTrace_4947608 : CollatzResearch.WordTrace tailWord_4947608 prefixEnd_4947608 282277888225575966071819 := by
  unfold tailWord_4947608
  simp only [CollatzResearch.WordTrace]
  refine ⟨90227044329834337509441739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120302725773112450012588985 90227044329834337509441739)
  ·
    refine ⟨135340566494751506264162609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90227044329834337509441739 135340566494751506264162609)
    ·
      refine ⟨101505424871063629698121957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135340566494751506264162609 101505424871063629698121957)
      ·
        refine ⟨19032267163324430568397867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101505424871063629698121957 19032267163324430568397867)
        ·
          refine ⟨28548400744986645852596801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19032267163324430568397867 28548400744986645852596801)
          ·
            refine ⟨21411300558739984389447601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28548400744986645852596801 21411300558739984389447601)
            ·
              refine ⟨16058475419054988292085701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21411300558739984389447601 16058475419054988292085701)
              ·
                refine ⟨3010964141072810304766069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16058475419054988292085701 3010964141072810304766069)
                ·
                  refine ⟨282277888225575966071819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3010964141072810304766069 282277888225575966071819)
                  ·
                    rfl

theorem cell23_4947608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 5].length) (baseStart_4947608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947608 prefixEnd_4947608 := by exact prefixLift 4947608
  have htrace : WordTrace (prefixWord ++ tailWord_4947608) baseStart_4947608 baseEnd_4947608 := by
    simpa [prefixWord, tailWord_4947608, baseEnd_4947608] using wordTrace_append hprefix tailTrace_4947608
  have hstable : (prefixWord ++ tailWord_4947608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947608).length < 2 ^ (prefixWord ++ tailWord_4947608).sum := by decide
  have hdescent : baseEnd_4947608 < baseStart_4947608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947641 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 1, 3, 4]
def baseStart_4947641 : Nat := 118140960795 + 4947641 * 2 ^ 59
def prefixEnd_4947641 : Nat := 4983230072969 + 3 ^ 40 * 4947641 * 2
def baseEnd_4947641 : Nat := 2540517938891782065533719

theorem tailTrace_4947641 : CollatzResearch.WordTrace tailWord_4947641 prefixEnd_4947641 2540517938891782065533719 := by
  unfold tailWord_4947641
  simp only [CollatzResearch.WordTrace]
  refine ⟨180455292268549121654834777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120303528179032747769889851 180455292268549121654834777)
  ·
    refine ⟨135341469201411841241126083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180455292268549121654834777 135341469201411841241126083)
    ·
      refine ⟨203012203802117761861689125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135341469201411841241126083 203012203802117761861689125)
      ·
        refine ⟨38064788212897080349066711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203012203802117761861689125 38064788212897080349066711)
        ·
          refine ⟨57097182319345620523600067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38064788212897080349066711 57097182319345620523600067)
          ·
            refine ⟨85645773479018430785400101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57097182319345620523600067 85645773479018430785400101)
            ·
              refine ⟨16058582527315955772262519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85645773479018430785400101 16058582527315955772262519)
              ·
                refine ⟨24087873790973933658393779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16058582527315955772262519 24087873790973933658393779)
                ·
                  refine ⟨36131810686460900487590669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24087873790973933658393779 36131810686460900487590669)
                  ·
                    refine ⟨13549429007422837682846501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36131810686460900487590669 13549429007422837682846501)
                    ·
                      refine ⟨2540517938891782065533719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13549429007422837682846501 2540517938891782065533719)
                      ·
                        rfl

theorem cell23_4947641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_4947641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947641 prefixEnd_4947641 := by exact prefixLift 4947641
  have htrace : WordTrace (prefixWord ++ tailWord_4947641) baseStart_4947641 baseEnd_4947641 := by
    simpa [prefixWord, tailWord_4947641, baseEnd_4947641] using wordTrace_append hprefix tailTrace_4947641
  have hstable : (prefixWord ++ tailWord_4947641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947641).length < 2 ^ (prefixWord ++ tailWord_4947641).sum := by decide
  have hdescent : baseEnd_4947641 < baseStart_4947641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947670 : List Nat := [5, 2, 1, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_4947670 : Nat := 118140960795 + 4947670 * 2 ^ 59
def prefixEnd_4947670 : Nat := 4983230072969 + 3 ^ 40 * 4947670 * 2
def baseEnd_4947670 : Nat := 2540532829830762452071087

theorem tailTrace_4947670 : CollatzResearch.WordTrace tailWord_4947670 prefixEnd_4947670 2540532829830762452071087 := by
  unfold tailWord_4947670
  simp only [CollatzResearch.WordTrace]
  refine ⟨11278521874090253725477529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120304233323629373071760309 11278521874090253725477529)
  ·
    refine ⟨8458891405567690294108147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11278521874090253725477529 8458891405567690294108147)
    ·
      refine ⟨12688337108351535441162221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8458891405567690294108147 12688337108351535441162221)
      ·
        refine ⟨4758126415631825790435833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12688337108351535441162221 4758126415631825790435833)
        ·
          refine ⟨3568594811723869342826875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4758126415631825790435833 3568594811723869342826875)
          ·
            refine ⟨5352892217585804014240313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3568594811723869342826875 5352892217585804014240313)
            ·
              refine ⟨4014669163189353010680235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5352892217585804014240313 4014669163189353010680235)
              ·
                refine ⟨6022003744784029516020353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4014669163189353010680235 6022003744784029516020353)
                ·
                  refine ⟨4516502808588022137015265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6022003744784029516020353 4516502808588022137015265)
                  ·
                    refine ⟨3387377106441016602761449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4516502808588022137015265 3387377106441016602761449)
                    ·
                      refine ⟨2540532829830762452071087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3387377106441016602761449 2540532829830762452071087)
                      ·
                        rfl

theorem cell23_4947670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_4947670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947670 prefixEnd_4947670 := by exact prefixLift 4947670
  have htrace : WordTrace (prefixWord ++ tailWord_4947670) baseStart_4947670 baseEnd_4947670 := by
    simpa [prefixWord, tailWord_4947670, baseEnd_4947670] using wordTrace_append hprefix tailTrace_4947670
  have hstable : (prefixWord ++ tailWord_4947670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947670).length < 2 ^ (prefixWord ++ tailWord_4947670).sum := by decide
  have hdescent : baseEnd_4947670 < baseStart_4947670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947691 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 3]
def baseStart_4947691 : Nat := 118140960795 + 4947691 * 2 ^ 59
def prefixEnd_4947691 : Nat := 4983230072969 + 3 ^ 40 * 4947691 * 2
def baseEnd_4947691 : Nat := 2540543612924506869908489

theorem tailTrace_4947691 : CollatzResearch.WordTrace tailWord_4947691 prefixEnd_4947691 2540543612924506869908489 := by
  unfold tailWord_4947691
  simp only [CollatzResearch.WordTrace]
  refine ⟨180457115918367980194154927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120304743945578653462769951 180457115918367980194154927)
  ·
    refine ⟨270685673877551970291232391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180457115918367980194154927 270685673877551970291232391)
    ·
      refine ⟨406028510816327955436848587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270685673877551970291232391 406028510816327955436848587)
      ·
        refine ⟨609042766224491933155272881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406028510816327955436848587 609042766224491933155272881)
        ·
          refine ⟨456782074668368949866454661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 609042766224491933155272881 456782074668368949866454661)
          ·
            refine ⟨85646639000319178099960249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 456782074668368949866454661 85646639000319178099960249)
            ·
              refine ⟨64234979250239383574970187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85646639000319178099960249 64234979250239383574970187)
              ·
                refine ⟨96352468875359075362455281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64234979250239383574970187 96352468875359075362455281)
                ·
                  refine ⟨72264351656519306521841461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96352468875359075362455281 72264351656519306521841461)
                  ·
                    refine ⟨6774782967798684986422637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72264351656519306521841461 6774782967798684986422637)
                    ·
                      refine ⟨2540543612924506869908489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6774782967798684986422637 2540543612924506869908489)
                      ·
                        rfl

theorem cell23_4947691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 3].length) (baseStart_4947691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947691 prefixEnd_4947691 := by exact prefixLift 4947691
  have htrace : WordTrace (prefixWord ++ tailWord_4947691) baseStart_4947691 baseEnd_4947691 := by
    simpa [prefixWord, tailWord_4947691, baseEnd_4947691] using wordTrace_append hprefix tailTrace_4947691
  have hstable : (prefixWord ++ tailWord_4947691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947691).length < 2 ^ (prefixWord ++ tailWord_4947691).sum := by decide
  have hdescent : baseEnd_4947691 < baseStart_4947691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947752 : List Nat := [2, 1, 5, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_4947752 : Nat := 118140960795 + 4947752 * 2 ^ 59
def prefixEnd_4947752 : Nat := 4983230072969 + 3 ^ 40 * 4947752 * 2
def baseEnd_4947752 : Nat := 2540574935244431131245709

theorem tailTrace_4947752 : CollatzResearch.WordTrace tailWord_4947752 prefixEnd_4947752 2540574935244431131245709 := by
  unfold tailWord_4947752
  simp only [CollatzResearch.WordTrace]
  refine ⟨90229670385573493806062755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120306227180764658408083673 90229670385573493806062755)
  ·
    refine ⟨135344505578360240709094133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90229670385573493806062755 135344505578360240709094133)
    ·
      refine ⟨12688547397971272566477575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135344505578360240709094133 12688547397971272566477575)
      ·
        refine ⟨19032821096956908849716363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12688547397971272566477575 19032821096956908849716363)
        ·
          refine ⟨28549231645435363274574545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19032821096956908849716363 28549231645435363274574545)
          ·
            refine ⟨21411923734076522455930909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28549231645435363274574545 21411923734076522455930909)
            ·
              refine ⟨8029471400278695920974091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21411923734076522455930909 8029471400278695920974091)
              ·
                refine ⟨12044207100418043881461137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8029471400278695920974091 12044207100418043881461137)
                ·
                  refine ⟨9033155325313532911095853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12044207100418043881461137 9033155325313532911095853)
                  ·
                    refine ⟨3387433246992574841660945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9033155325313532911095853 3387433246992574841660945)
                    ·
                      refine ⟨2540574935244431131245709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3387433246992574841660945 2540574935244431131245709)
                      ·
                        rfl

theorem cell23_4947752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_4947752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947752 prefixEnd_4947752 := by exact prefixLift 4947752
  have htrace : WordTrace (prefixWord ++ tailWord_4947752) baseStart_4947752 baseEnd_4947752 := by
    simpa [prefixWord, tailWord_4947752, baseEnd_4947752] using wordTrace_append hprefix tailTrace_4947752
  have hstable : (prefixWord ++ tailWord_4947752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947752).length < 2 ^ (prefixWord ++ tailWord_4947752).sum := by decide
  have hdescent : baseEnd_4947752 < baseStart_4947752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947762 : List Nat := [3, 2, 1, 1, 3, 4, 2, 1, 1, 5]
def baseStart_4947762 : Nat := 118140960795 + 4947762 * 2 ^ 59
def prefixEnd_4947762 : Nat := 4983230072969 + 3 ^ 40 * 4947762 * 2
def baseEnd_4947762 : Nat := 846860023350325364040221

theorem tailTrace_4947762 : CollatzResearch.WordTrace tailWord_4947762 prefixEnd_4947762 846860023350325364040221 := by
  unfold tailWord_4947762
  simp only [CollatzResearch.WordTrace]
  refine ⟨45114926375277689829997385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120306470334073839546659693 45114926375277689829997385)
  ·
    refine ⟨33836194781458267372498039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45114926375277689829997385 33836194781458267372498039)
    ·
      refine ⟨50754292172187401058747059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33836194781458267372498039 50754292172187401058747059)
      ·
        refine ⟨76131438258281101588120589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50754292172187401058747059 76131438258281101588120589)
        ·
          refine ⟨28549289346855413095545221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76131438258281101588120589 28549289346855413095545221)
          ·
            refine ⟨5352991752535389955414729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28549289346855413095545221 5352991752535389955414729)
            ·
              refine ⟨4014743814401542466561047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5352991752535389955414729 4014743814401542466561047)
              ·
                refine ⟨6022115721602313699841571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4014743814401542466561047 6022115721602313699841571)
                ·
                  refine ⟨9033173582403470549762357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6022115721602313699841571 9033173582403470549762357)
                  ·
                    refine ⟨846860023350325364040221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9033173582403470549762357 846860023350325364040221)
                    ·
                      rfl

theorem cell23_4947762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_4947762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947762 prefixEnd_4947762 := by exact prefixLift 4947762
  have htrace : WordTrace (prefixWord ++ tailWord_4947762) baseStart_4947762 baseEnd_4947762 := by
    simpa [prefixWord, tailWord_4947762, baseEnd_4947762] using wordTrace_append hprefix tailTrace_4947762
  have hstable : (prefixWord ++ tailWord_4947762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947762).length < 2 ^ (prefixWord ++ tailWord_4947762).sum := by decide
  have hdescent : baseEnd_4947762 < baseStart_4947762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947775 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 4, 4]
def baseStart_4947775 : Nat := 118140960795 + 4947775 * 2 ^ 59
def prefixEnd_4947775 : Nat := 4983230072969 + 3 ^ 40 * 4947775 * 2
def baseEnd_4947775 : Nat := 846862248433161513752701

theorem tailTrace_4947775 : CollatzResearch.WordTrace tailWord_4947775 prefixEnd_4947775 846862248433161513752701 := by
  unfold tailWord_4947775
  simp only [CollatzResearch.WordTrace]
  refine ⟨180460179650063662540212779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120306786433375775026808519 180460179650063662540212779)
  ·
    refine ⟨270690269475095493810319169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180460179650063662540212779 270690269475095493810319169)
    ·
      refine ⟨203017702106321620357739377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270690269475095493810319169 203017702106321620357739377)
      ·
        refine ⟨152263276579741215268304533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203017702106321620357739377 152263276579741215268304533)
        ·
          refine ⟨7137341089675369465701775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 152263276579741215268304533 7137341089675369465701775)
          ·
            refine ⟨10706011634513054198552663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7137341089675369465701775 10706011634513054198552663)
            ·
              refine ⟨16059017451769581297828995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10706011634513054198552663 16059017451769581297828995)
              ·
                refine ⟨24088526177654371946743493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16059017451769581297828995 24088526177654371946743493)
                ·
                  refine ⟨4516598658310194740014405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24088526177654371946743493 4516598658310194740014405)
                  ·
                    refine ⟨846862248433161513752701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4516598658310194740014405 846862248433161513752701)
                    ·
                      rfl

theorem cell23_4947775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 4].length) (baseStart_4947775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947775 prefixEnd_4947775 := by exact prefixLift 4947775
  have htrace : WordTrace (prefixWord ++ tailWord_4947775) baseStart_4947775 baseEnd_4947775 := by
    simpa [prefixWord, tailWord_4947775, baseEnd_4947775] using wordTrace_append hprefix tailTrace_4947775
  have hstable : (prefixWord ++ tailWord_4947775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947775).length < 2 ^ (prefixWord ++ tailWord_4947775).sum := by decide
  have hdescent : baseEnd_4947775 < baseStart_4947775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947815 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 6, 1, 3]
def baseStart_4947815 : Nat := 118140960795 + 4947815 * 2 ^ 59
def prefixEnd_4947815 : Nat := 4983230072969 + 3 ^ 40 * 4947815 * 2
def baseEnd_4947815 : Nat := 2540607284525664384757919

theorem tailTrace_4947815 : CollatzResearch.WordTrace tailWord_4947815 prefixEnd_4947815 2540607284525664384757919 := by
  unfold tailWord_4947815
  simp only [CollatzResearch.WordTrace]
  refine ⟨180461638569918749371668899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120307759046612499581112599 180461638569918749371668899)
  ·
    refine ⟨270692457854878124057503349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180461638569918749371668899 270692457854878124057503349)
    ·
      refine ⟨25377417923894824130390939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 270692457854878124057503349 25377417923894824130390939)
      ·
        refine ⟨38066126885842236195586409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25377417923894824130390939 38066126885842236195586409)
        ·
          refine ⟨28549595164381677146689807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38066126885842236195586409 28549595164381677146689807)
          ·
            refine ⟨42824392746572515720034711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28549595164381677146689807 42824392746572515720034711)
            ·
              refine ⟨64236589119858773580052067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42824392746572515720034711 64236589119858773580052067)
              ·
                refine ⟨96354883679788160370078101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64236589119858773580052067 96354883679788160370078101)
                ·
                  refine ⟨4516635172490070017347411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 96354883679788160370078101 4516635172490070017347411)
                  ·
                    refine ⟨6774952758735105026021117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4516635172490070017347411 6774952758735105026021117)
                    ·
                      refine ⟨2540607284525664384757919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6774952758735105026021117 2540607284525664384757919)
                      ·
                        rfl

theorem cell23_4947815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_4947815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947815 prefixEnd_4947815 := by exact prefixLift 4947815
  have htrace : WordTrace (prefixWord ++ tailWord_4947815) baseStart_4947815 baseEnd_4947815 := by
    simpa [prefixWord, tailWord_4947815, baseEnd_4947815] using wordTrace_append hprefix tailTrace_4947815
  have hstable : (prefixWord ++ tailWord_4947815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947815).length < 2 ^ (prefixWord ++ tailWord_4947815).sum := by decide
  have hdescent : baseEnd_4947815 < baseStart_4947815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947888 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 3]
def baseStart_4947888 : Nat := 118140960795 + 4947888 * 2 ^ 59
def prefixEnd_4947888 : Nat := 4983230072969 + 3 ^ 40 * 4947888 * 2
def baseEnd_4947888 : Nat := 2540644768613442599145083

theorem tailTrace_4947888 : CollatzResearch.WordTrace tailWord_4947888 prefixEnd_4947888 2540644768613442599145083 := by
  unfold tailWord_4947888
  simp only [CollatzResearch.WordTrace]
  refine ⟨90232150549327141419538159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120309534065769521892717545 90232150549327141419538159)
  ·
    refine ⟨135348225823990712129307239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90232150549327141419538159 135348225823990712129307239)
    ·
      refine ⟨203022338735986068193960859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135348225823990712129307239 203022338735986068193960859)
      ·
        refine ⟨304533508103979102290941289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203022338735986068193960859 304533508103979102290941289)
        ·
          refine ⟨228400131077984326718205967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304533508103979102290941289 228400131077984326718205967)
          ·
            refine ⟨342600196616976490077308951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228400131077984326718205967 342600196616976490077308951)
            ·
              refine ⟨513900294925464735115963427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342600196616976490077308951 513900294925464735115963427)
              ·
                refine ⟨770850442388197102673945141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 513900294925464735115963427 770850442388197102673945141)
                ·
                  refine ⟨72267228973893478375682357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 770850442388197102673945141 72267228973893478375682357)
                  ·
                    refine ⟨6775052716302513597720221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72267228973893478375682357 6775052716302513597720221)
                    ·
                      refine ⟨2540644768613442599145083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6775052716302513597720221 2540644768613442599145083)
                      ·
                        rfl

theorem cell23_4947888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 3].length) (baseStart_4947888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947888 prefixEnd_4947888 := by exact prefixLift 4947888
  have htrace : WordTrace (prefixWord ++ tailWord_4947888) baseStart_4947888 baseEnd_4947888 := by
    simpa [prefixWord, tailWord_4947888, baseEnd_4947888] using wordTrace_append hprefix tailTrace_4947888
  have hstable : (prefixWord ++ tailWord_4947888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947888).length < 2 ^ (prefixWord ++ tailWord_4947888).sum := by decide
  have hdescent : baseEnd_4947888 < baseStart_4947888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947889 : List Nat := [1, 2, 2, 4, 2, 1, 1, 4, 2, 2, 2]
def baseStart_4947889 : Nat := 118140960795 + 4947889 * 2 ^ 59
def prefixEnd_4947889 : Nat := 4983230072969 + 3 ^ 40 * 4947889 * 2
def baseEnd_4947889 : Nat := 2540645282094097095232579

theorem tailTrace_4947889 : CollatzResearch.WordTrace tailWord_4947889 prefixEnd_4947889 2540645282094097095232579 := by
  unfold tailWord_4947889
  simp only [CollatzResearch.WordTrace]
  refine ⟨180464337571650660009862721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120309558381100440006575147 180464337571650660009862721)
  ·
    refine ⟨135348253178737995007397041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180464337571650660009862721 135348253178737995007397041)
    ·
      refine ⟨101511189884053496255547781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135348253178737995007397041 101511189884053496255547781)
      ·
        refine ⟨19033348103260030547915209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101511189884053496255547781 19033348103260030547915209)
        ·
          refine ⟨14275011077445022910936407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19033348103260030547915209 14275011077445022910936407)
          ·
            refine ⟨21412516616167534366404611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14275011077445022910936407 21412516616167534366404611)
            ·
              refine ⟨32118774924251301549606917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21412516616167534366404611 32118774924251301549606917)
              ·
                refine ⟨6022270298297119040551297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32118774924251301549606917 6022270298297119040551297)
                ·
                  refine ⟨4516702723722839280413473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6022270298297119040551297 4516702723722839280413473)
                  ·
                    refine ⟨3387527042792129460310105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4516702723722839280413473 3387527042792129460310105)
                    ·
                      refine ⟨2540645282094097095232579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3387527042792129460310105 2540645282094097095232579)
                      ·
                        rfl

theorem cell23_4947889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_4947889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947889 prefixEnd_4947889 := by exact prefixLift 4947889
  have htrace : WordTrace (prefixWord ++ tailWord_4947889) baseStart_4947889 baseEnd_4947889 := by
    simpa [prefixWord, tailWord_4947889, baseEnd_4947889] using wordTrace_append hprefix tailTrace_4947889
  have hstable : (prefixWord ++ tailWord_4947889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947889).length < 2 ^ (prefixWord ++ tailWord_4947889).sum := by decide
  have hdescent : baseEnd_4947889 < baseStart_4947889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947915 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 2, 5, 2]
def baseStart_4947915 : Nat := 118140960795 + 4947915 * 2 ^ 59
def prefixEnd_4947915 : Nat := 4983230072969 + 3 ^ 40 * 4947915 * 2
def baseEnd_4947915 : Nat := 2540658632591113993507459

theorem tailTrace_4947915 : CollatzResearch.WordTrace tailWord_4947915 prefixEnd_4947915 2540658632591113993507459 := by
  unfold tailWord_4947915
  simp only [CollatzResearch.WordTrace]
  refine ⟨180465285869556466450309199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120310190579704310966872799 180465285869556466450309199)
  ·
    refine ⟨270697928804334699675463799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180465285869556466450309199 270697928804334699675463799)
    ·
      refine ⟨406046893206502049513195699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270697928804334699675463799 406046893206502049513195699)
      ·
        refine ⟨609070339809753074269793549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406046893206502049513195699 609070339809753074269793549)
        ·
          refine ⟨228401377428657402851172581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 609070339809753074269793549 228401377428657402851172581)
          ·
            refine ⟨42825258267873263034594859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228401377428657402851172581 42825258267873263034594859)
            ·
              refine ⟨64237887401809894551892289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42825258267873263034594859 64237887401809894551892289)
              ·
                refine ⟨48178415551357420913919217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64237887401809894551892289 48178415551357420913919217)
                ·
                  refine ⟨36133811663518065685439413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48178415551357420913919217 36133811663518065685439413)
                  ·
                    refine ⟨3387544843454818658009945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36133811663518065685439413 3387544843454818658009945)
                    ·
                      refine ⟨2540658632591113993507459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3387544843454818658009945 2540658632591113993507459)
                      ·
                        rfl

theorem cell23_4947915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 5, 2].length) (baseStart_4947915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947915 prefixEnd_4947915 := by exact prefixLift 4947915
  have htrace : WordTrace (prefixWord ++ tailWord_4947915) baseStart_4947915 baseEnd_4947915 := by
    simpa [prefixWord, tailWord_4947915, baseEnd_4947915] using wordTrace_append hprefix tailTrace_4947915
  have hstable : (prefixWord ++ tailWord_4947915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947915).length < 2 ^ (prefixWord ++ tailWord_4947915).sum := by decide
  have hdescent : baseEnd_4947915 < baseStart_4947915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947925 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 1, 7]
def baseStart_4947925 : Nat := 118140960795 + 4947925 * 2 ^ 59
def prefixEnd_4947925 : Nat := 4983230072969 + 3 ^ 40 * 4947925 * 2
def baseEnd_4947925 : Nat := 846887922465886318127471

theorem tailTrace_4947925 : CollatzResearch.WordTrace tailWord_4947925 prefixEnd_4947925 846887922465886318127471 := by
  unfold tailWord_4947925
  simp only [CollatzResearch.WordTrace]
  refine ⟨180465650599520238158173229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120310433733013492105448819 180465650599520238158173229)
  ·
    refine ⟨67674618974820089309314961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180465650599520238158173229 67674618974820089309314961)
    ·
      refine ⟨50755964231115066981986221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67674618974820089309314961 50755964231115066981986221)
      ·
        refine ⟨19033486586668150118244833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50755964231115066981986221 19033486586668150118244833)
        ·
          refine ⟨14275114940001112588683625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19033486586668150118244833 14275114940001112588683625)
          ·
            refine ⟨10706336205000834441512719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14275114940001112588683625 10706336205000834441512719)
            ·
              refine ⟨16059504307501251662269079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10706336205000834441512719 16059504307501251662269079)
              ·
                refine ⟨24089256461251877493403619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16059504307501251662269079 24089256461251877493403619)
                ·
                  refine ⟨36133884691877816240105429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24089256461251877493403619 36133884691877816240105429)
                  ·
                    refine ⟨846887922465886318127471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36133884691877816240105429 846887922465886318127471)
                    ·
                      rfl

theorem cell23_4947925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_4947925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947925 prefixEnd_4947925 := by exact prefixLift 4947925
  have htrace : WordTrace (prefixWord ++ tailWord_4947925) baseStart_4947925 baseEnd_4947925 := by
    simpa [prefixWord, tailWord_4947925, baseEnd_4947925] using wordTrace_append hprefix tailTrace_4947925
  have hstable : (prefixWord ++ tailWord_4947925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947925).length < 2 ^ (prefixWord ++ tailWord_4947925).sum := by decide
  have hdescent : baseEnd_4947925 < baseStart_4947925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947948 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 5]
def baseStart_4947948 : Nat := 118140960795 + 4947948 * 2 ^ 59
def prefixEnd_4947948 : Nat := 4983230072969 + 3 ^ 40 * 4947948 * 2
def baseEnd_4947948 : Nat := 2540675577452712364394807

theorem tailTrace_4947948 : CollatzResearch.WordTrace tailWord_4947948 prefixEnd_4947948 2540675577452712364394807 := by
  unfold tailWord_4947948
  simp only [CollatzResearch.WordTrace]
  refine ⟨90233244739218456543130249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120310992985624608724173665 90233244739218456543130249)
  ·
    refine ⟨67674933554413842407347687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90233244739218456543130249 67674933554413842407347687)
    ·
      refine ⟨101512400331620763611021531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67674933554413842407347687 101512400331620763611021531)
      ·
        refine ⟨152268600497431145416532297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101512400331620763611021531 152268600497431145416532297)
        ·
          refine ⟨114201450373073359062399223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152268600497431145416532297 114201450373073359062399223)
          ·
            refine ⟨171302175559610038593598835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114201450373073359062399223 171302175559610038593598835)
            ·
              refine ⟨256953263339415057890398253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171302175559610038593598835 256953263339415057890398253)
              ·
                refine ⟨96357473752280646708899345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 256953263339415057890398253 96357473752280646708899345)
                ·
                  refine ⟨72268105314210485031674509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96357473752280646708899345 72268105314210485031674509)
                  ·
                    refine ⟨27100539492828931886877941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72268105314210485031674509 27100539492828931886877941)
                    ·
                      refine ⟨2540675577452712364394807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27100539492828931886877941 2540675577452712364394807)
                      ·
                        rfl

theorem cell23_4947948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_4947948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947948 prefixEnd_4947948 := by exact prefixLift 4947948
  have htrace : WordTrace (prefixWord ++ tailWord_4947948) baseStart_4947948 baseEnd_4947948 := by
    simpa [prefixWord, tailWord_4947948, baseEnd_4947948] using wordTrace_append hprefix tailTrace_4947948
  have hstable : (prefixWord ++ tailWord_4947948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947948).length < 2 ^ (prefixWord ++ tailWord_4947948).sum := by decide
  have hdescent : baseEnd_4947948 < baseStart_4947948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947965 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 1, 4, 3]
def baseStart_4947965 : Nat := 118140960795 + 4947965 * 2 ^ 59
def prefixEnd_4947965 : Nat := 4983230072969 + 3 ^ 40 * 4947965 * 2
def baseEnd_4947965 : Nat := 2540684306623838797882229

theorem tailTrace_4947965 : CollatzResearch.WordTrace tailWord_4947965 prefixEnd_4947965 2540684306623838797882229 := by
  unfold tailWord_4947965
  simp only [CollatzResearch.WordTrace]
  refine ⟨180467109519375324989629349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120311406346250216659752899 180467109519375324989629349)
  ·
    refine ⟨33837583034882873435555503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180467109519375324989629349 33837583034882873435555503)
    ·
      refine ⟨50756374552324310153333255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33837583034882873435555503 50756374552324310153333255)
      ·
        refine ⟨76134561828486465229999883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50756374552324310153333255 76134561828486465229999883)
        ·
          refine ⟨114201842742729697844999825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76134561828486465229999883 114201842742729697844999825)
          ·
            refine ⟨85651382057047273383749869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114201842742729697844999825 85651382057047273383749869)
            ·
              refine ⟨32119268271392727518906201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85651382057047273383749869 32119268271392727518906201)
              ·
                refine ⟨24089451203544545639179651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32119268271392727518906201 24089451203544545639179651)
                ·
                  refine ⟨36134176805316818458769477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24089451203544545639179651 36134176805316818458769477)
                  ·
                    refine ⟨6775158150996903461019277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36134176805316818458769477 6775158150996903461019277)
                    ·
                      refine ⟨2540684306623838797882229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6775158150996903461019277 2540684306623838797882229)
                      ·
                        rfl

theorem cell23_4947965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_4947965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947965 prefixEnd_4947965 := by exact prefixLift 4947965
  have htrace : WordTrace (prefixWord ++ tailWord_4947965) baseStart_4947965 baseEnd_4947965 := by
    simpa [prefixWord, tailWord_4947965, baseEnd_4947965] using wordTrace_append hprefix tailTrace_4947965
  have hstable : (prefixWord ++ tailWord_4947965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947965).length < 2 ^ (prefixWord ++ tailWord_4947965).sum := by decide
  have hdescent : baseEnd_4947965 < baseStart_4947965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4947982 : List Nat := [4, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3]
def baseStart_4947982 : Nat := 118140960795 + 4947982 * 2 ^ 59
def prefixEnd_4947982 : Nat := 4983230072969 + 3 ^ 40 * 4947982 * 2
def baseEnd_4947982 : Nat := 2540693035794965231369651

theorem tailTrace_4947982 : CollatzResearch.WordTrace tailWord_4947982 prefixEnd_4947982 2540693035794965231369651 := by
  unfold tailWord_4947982
  simp only [CollatzResearch.WordTrace]
  refine ⟨22558466195039217111624775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120311819706875824595332133 22558466195039217111624775)
  ·
    refine ⟨33837699292558825667437163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22558466195039217111624775 33837699292558825667437163)
    ·
      refine ⟨50756548938838238501155745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33837699292558825667437163 50756548938838238501155745)
      ·
        refine ⟨38067411704128678875866809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50756548938838238501155745 38067411704128678875866809)
        ·
          refine ⟨28550558778096509156900107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38067411704128678875866809 28550558778096509156900107)
          ·
            refine ⟨42825838167144763735350161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28550558778096509156900107 42825838167144763735350161)
            ·
              refine ⟨32119378625358572801512621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42825838167144763735350161 32119378625358572801512621)
              ·
                refine ⟨12044766984509464800567233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32119378625358572801512621 12044766984509464800567233)
                ·
                  refine ⟨9033575238382098600425425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12044766984509464800567233 9033575238382098600425425)
                  ·
                    refine ⟨6775181428786573950319069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9033575238382098600425425 6775181428786573950319069)
                    ·
                      refine ⟨2540693035794965231369651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6775181428786573950319069 2540693035794965231369651)
                      ·
                        rfl

theorem cell23_4947982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_4947982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4947982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4947982 prefixEnd_4947982 := by exact prefixLift 4947982
  have htrace : WordTrace (prefixWord ++ tailWord_4947982) baseStart_4947982 baseEnd_4947982 := by
    simpa [prefixWord, tailWord_4947982, baseEnd_4947982] using wordTrace_append hprefix tailTrace_4947982
  have hstable : (prefixWord ++ tailWord_4947982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4947982).length < 2 ^ (prefixWord ++ tailWord_4947982).sum := by decide
  have hdescent : baseEnd_4947982 < baseStart_4947982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4947982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948012 : List Nat := [2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 3]
def baseStart_4948012 : Nat := 118140960795 + 4948012 * 2 ^ 59
def prefixEnd_4948012 : Nat := 4983230072969 + 3 ^ 40 * 4948012 * 2
def baseEnd_4948012 : Nat := 2540708440214600113994513

theorem tailTrace_4948012 : CollatzResearch.WordTrace tailWord_4948012 prefixEnd_4948012 2540708440214600113994513 := by
  unfold tailWord_4948012
  simp only [CollatzResearch.WordTrace]
  refine ⟨90234411875102526008295145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120312549166803368011060193 90234411875102526008295145)
  ·
    refine ⟨67675808906326894506221359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90234411875102526008295145 67675808906326894506221359)
    ·
      refine ⟨101513713359490341759332039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67675808906326894506221359 101513713359490341759332039)
      ·
        refine ⟨152270570039235512638998059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101513713359490341759332039 152270570039235512638998059)
        ·
          refine ⟨228405855058853268958497089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152270570039235512638998059 228405855058853268958497089)
          ·
            refine ⟨171304391294139951718872817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228405855058853268958497089 171304391294139951718872817)
            ·
              refine ⟨128478293470604963789154613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171304391294139951718872817 128478293470604963789154613)
              ·
                refine ⟨12044840012869215355233245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128478293470604963789154613 12044840012869215355233245)
                ·
                  refine ⟨4516815004825955758212467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12044840012869215355233245 4516815004825955758212467)
                  ·
                    refine ⟨6775222507238933637318701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4516815004825955758212467 6775222507238933637318701)
                    ·
                      refine ⟨2540708440214600113994513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6775222507238933637318701 2540708440214600113994513)
                      ·
                        rfl

theorem cell23_4948012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 3].length) (baseStart_4948012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948012 prefixEnd_4948012 := by exact prefixLift 4948012
  have htrace : WordTrace (prefixWord ++ tailWord_4948012) baseStart_4948012 baseEnd_4948012 := by
    simpa [prefixWord, tailWord_4948012, baseEnd_4948012] using wordTrace_append hprefix tailTrace_4948012
  have hstable : (prefixWord ++ tailWord_4948012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948012).length < 2 ^ (prefixWord ++ tailWord_4948012).sum := by decide
  have hdescent : baseEnd_4948012 < baseStart_4948012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
