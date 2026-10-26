import V185TrunkScan22Chunk127

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1145898 : List Nat := [3, 1, 4, 1, 3, 1, 2, 3, 1, 3]
def baseStart_1145898 : Nat := 118140960795 + 1145898 * 2 ^ 59
def prefixEnd_1145898 : Nat := 4983230072969 + 3 ^ 40 * 1145898 * 2
def baseEnd_1145898 : Nat := 392264303350575268336745

theorem tailTrace_1145898 : CollatzResearch.WordTrace tailWord_1145898 prefixEnd_1145898 392264303350575268336745 := by
  unfold tailWord_1145898
  simp only [CollatzResearch.WordTrace]
  refine ⟨10448583400653681160683587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27862889068409816428489565 10448583400653681160683587)
  ·
    refine ⟨15672875100980521741025381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10448583400653681160683587 15672875100980521741025381)
    ·
      refine ⟨2938664081433847826442259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15672875100980521741025381 2938664081433847826442259)
      ·
        refine ⟨4407996122150771739663389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2938664081433847826442259 4407996122150771739663389)
        ·
          refine ⟨1652998545806539402373771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4407996122150771739663389 1652998545806539402373771)
          ·
            refine ⟨2479497818709809103560657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1652998545806539402373771 2479497818709809103560657)
            ·
              refine ⟨1859623364032356827670493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2479497818709809103560657 1859623364032356827670493)
              ·
                refine ⟨697358761512133810376435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1859623364032356827670493 697358761512133810376435)
                ·
                  refine ⟨1046038142268200715564653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 697358761512133810376435 1046038142268200715564653)
                  ·
                    refine ⟨392264303350575268336745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1046038142268200715564653 392264303350575268336745)
                    ·
                      rfl

theorem cell22_1145898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_1145898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145898 prefixEnd_1145898 := by exact prefixLift 1145898
  have htrace : WordTrace (prefixWord ++ tailWord_1145898) baseStart_1145898 baseEnd_1145898 := by
    simpa [prefixWord, tailWord_1145898, baseEnd_1145898] using wordTrace_append hprefix tailTrace_1145898
  have hstable : (prefixWord ++ tailWord_1145898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145898).length < 2 ^ (prefixWord ++ tailWord_1145898).sum := by decide
  have hdescent : baseEnd_1145898 < baseStart_1145898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145905 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 8]
def baseStart_1145905 : Nat := 118140960795 + 1145905 * 2 ^ 59
def prefixEnd_1145905 : Nat := 4983230072969 + 3 ^ 40 * 1145905 * 2
def baseEnd_1145905 : Nat := 130755566531209861137241

theorem tailTrace_1145905 : CollatzResearch.WordTrace tailWord_1145905 prefixEnd_1145905 130755566531209861137241 := by
  unfold tailWord_1145905
  simp only [CollatzResearch.WordTrace]
  refine ⟨41794588913589364838239169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27863059275726243225492779 41794588913589364838239169)
  ·
    refine ⟨31345941685192023628679377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41794588913589364838239169 31345941685192023628679377)
    ·
      refine ⟨23509456263894017721509533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31345941685192023628679377 23509456263894017721509533)
      ·
        refine ⟨8816046098960256645566075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23509456263894017721509533 8816046098960256645566075)
        ·
          refine ⟨13224069148440384968349113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8816046098960256645566075 13224069148440384968349113)
          ·
            refine ⟨9918051861330288726261835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13224069148440384968349113 9918051861330288726261835)
            ·
              refine ⟨14877077791995433089392753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9918051861330288726261835 14877077791995433089392753)
              ·
                refine ⟨11157808343996574817044565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14877077791995433089392753 11157808343996574817044565)
                ·
                  refine ⟨130755566531209861137241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11157808343996574817044565 130755566531209861137241)
                  ·
                    rfl

theorem cell22_1145905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 8].length) (baseStart_1145905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145905 prefixEnd_1145905 := by exact prefixLift 1145905
  have htrace : WordTrace (prefixWord ++ tailWord_1145905) baseStart_1145905 baseEnd_1145905 := by
    simpa [prefixWord, tailWord_1145905, baseEnd_1145905] using wordTrace_append hprefix tailTrace_1145905
  have hstable : (prefixWord ++ tailWord_1145905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145905).length < 2 ^ (prefixWord ++ tailWord_1145905).sum := by decide
  have hdescent : baseEnd_1145905 < baseStart_1145905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145937 : List Nat := [1, 2, 2, 1, 3, 1, 5, 1, 1, 5]
def baseStart_1145937 : Nat := 118140960795 + 1145937 * 2 ^ 59
def prefixEnd_1145937 : Nat := 4983230072969 + 3 ^ 40 * 1145937 * 2
def baseEnd_1145937 : Nat := 392277653847592166611625

theorem tailTrace_1145937 : CollatzResearch.WordTrace tailWord_1145937 prefixEnd_1145937 392277653847592166611625 := by
  unfold tailWord_1145937
  simp only [CollatzResearch.WordTrace]
  refine ⟨41795756049473434303404065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27863837366315622868936043 41795756049473434303404065)
  ·
    refine ⟨31346817037105075727553049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41795756049473434303404065 31346817037105075727553049)
    ·
      refine ⟨23510112777828806795664787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31346817037105075727553049 23510112777828806795664787)
      ·
        refine ⟨35265169166743210193497181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23510112777828806795664787 35265169166743210193497181)
        ·
          refine ⟨13224438437528703822561443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35265169166743210193497181 13224438437528703822561443)
          ·
            refine ⟨19836657656293055733842165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13224438437528703822561443 19836657656293055733842165)
            ·
              refine ⟨1859686655277473975047703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19836657656293055733842165 1859686655277473975047703)
              ·
                refine ⟨2789529982916210962571555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1859686655277473975047703 2789529982916210962571555)
                ·
                  refine ⟨4184294974374316443857333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2789529982916210962571555 4184294974374316443857333)
                  ·
                    refine ⟨392277653847592166611625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4184294974374316443857333 392277653847592166611625)
                    ·
                      rfl

theorem cell22_1145937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_1145937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145937 prefixEnd_1145937 := by exact prefixLift 1145937
  have htrace : WordTrace (prefixWord ++ tailWord_1145937) baseStart_1145937 baseEnd_1145937 := by
    simpa [prefixWord, tailWord_1145937, baseEnd_1145937] using wordTrace_append hprefix tailTrace_1145937
  have hstable : (prefixWord ++ tailWord_1145937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145937).length < 2 ^ (prefixWord ++ tailWord_1145937).sum := by decide
  have hdescent : baseEnd_1145937 < baseStart_1145937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145952 : List Nat := [2, 1, 1, 3, 2, 2, 2, 3, 2, 4]
def baseStart_1145952 : Nat := 118140960795 + 1145952 * 2 ^ 59
def prefixEnd_1145952 : Nat := 4983230072969 + 3 ^ 40 * 1145952 * 2
def baseEnd_1145952 : Nat := 392282788654137127486579

theorem tailTrace_1145952 : CollatzResearch.WordTrace tailWord_1145952 prefixEnd_1145952 392282788654137127486579 := by
  unfold tailWord_1145952
  simp only [CollatzResearch.WordTrace]
  refine ⟨20898151572209545932600055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27864202096279394576800073 20898151572209545932600055)
  ·
    refine ⟨31347227358314318898900083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20898151572209545932600055 31347227358314318898900083)
    ·
      refine ⟨47020841037471478348350125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31347227358314318898900083 47020841037471478348350125)
      ·
        refine ⟨17632815389051804380631297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47020841037471478348350125 17632815389051804380631297)
        ·
          refine ⟨13224611541788853285473473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17632815389051804380631297 13224611541788853285473473)
          ·
            refine ⟨9918458656341639964105105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13224611541788853285473473 9918458656341639964105105)
            ·
              refine ⟨7438843992256229973078829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9918458656341639964105105 7438843992256229973078829)
              ·
                refine ⟨2789566497096086239904561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7438843992256229973078829 2789566497096086239904561)
                ·
                  refine ⟨2092174872822064679928421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2789566497096086239904561 2092174872822064679928421)
                  ·
                    refine ⟨392282788654137127486579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2092174872822064679928421 392282788654137127486579)
                    ·
                      rfl

theorem cell22_1145952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 2, 4].length) (baseStart_1145952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145952 prefixEnd_1145952 := by exact prefixLift 1145952
  have htrace : WordTrace (prefixWord ++ tailWord_1145952) baseStart_1145952 baseEnd_1145952 := by
    simpa [prefixWord, tailWord_1145952, baseEnd_1145952] using wordTrace_append hprefix tailTrace_1145952
  have hstable : (prefixWord ++ tailWord_1145952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145952).length < 2 ^ (prefixWord ++ tailWord_1145952).sum := by decide
  have hdescent : baseEnd_1145952 < baseStart_1145952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145973 : List Nat := [1, 3, 4, 3, 2, 1, 1, 1, 6]
def baseStart_1145973 : Nat := 118140960795 + 1145973 * 2 ^ 59
def prefixEnd_1145973 : Nat := 4983230072969 + 3 ^ 40 * 1145973 * 2
def baseEnd_1145973 : Nat := 130763325794433357570505

theorem tailTrace_1145973 : CollatzResearch.WordTrace tailWord_1145973 prefixEnd_1145973 130763325794433357570505 := by
  unfold tailWord_1145973
  simp only [CollatzResearch.WordTrace]
  refine ⟨41797069077343012451714573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27864712718228674967809715 41797069077343012451714573)
  ·
    refine ⟨15673900904003629669392965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41797069077343012451714573 15673900904003629669392965)
    ·
      refine ⟨2938856419500680563011181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15673900904003629669392965 2938856419500680563011181)
      ·
        refine ⟨1102071157312755211129193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2938856419500680563011181 1102071157312755211129193)
        ·
          refine ⟨826553367984566408346895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1102071157312755211129193 826553367984566408346895)
          ·
            refine ⟨1239830051976849612520343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826553367984566408346895 1239830051976849612520343)
            ·
              refine ⟨1859745077965274418780515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1239830051976849612520343 1859745077965274418780515)
              ·
                refine ⟨2789617616947911628170773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1859745077965274418780515 2789617616947911628170773)
                ·
                  refine ⟨130763325794433357570505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2789617616947911628170773 130763325794433357570505)
                  ·
                    rfl

theorem cell22_1145973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 6].length) (baseStart_1145973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145973 prefixEnd_1145973 := by exact prefixLift 1145973
  have htrace : WordTrace (prefixWord ++ tailWord_1145973) baseStart_1145973 baseEnd_1145973 := by
    simpa [prefixWord, tailWord_1145973, baseEnd_1145973] using wordTrace_append hprefix tailTrace_1145973
  have hstable : (prefixWord ++ tailWord_1145973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145973).length < 2 ^ (prefixWord ++ tailWord_1145973).sum := by decide
  have hdescent : baseEnd_1145973 < baseStart_1145973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145988 : List Nat := [2, 3, 2, 1, 2, 4, 2, 1, 2, 3]
def baseStart_1145988 : Nat := 118140960795 + 1145988 * 2 ^ 59
def prefixEnd_1145988 : Nat := 4983230072969 + 3 ^ 40 * 1145988 * 2
def baseEnd_1145988 : Nat := 392295112189845033586469

theorem tailTrace_1145988 : CollatzResearch.WordTrace tailWord_1145988 prefixEnd_1145988 392295112189845033586469 := by
  unfold tailWord_1145988
  simp only [CollatzResearch.WordTrace]
  refine ⟨20898808086144335006755309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27865077448192446675673745 20898808086144335006755309)
  ·
    refine ⟨7837053032304125627533241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20898808086144335006755309 7837053032304125627533241)
    ·
      refine ⟨5877789774228094220649931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7837053032304125627533241 5877789774228094220649931)
      ·
        refine ⟨8816684661342141330974897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5877789774228094220649931 8816684661342141330974897)
        ·
          refine ⟨6612513496006605998231173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8816684661342141330974897 6612513496006605998231173)
          ·
            refine ⟨1239846280501238624668345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6612513496006605998231173 1239846280501238624668345)
            ·
              refine ⟨929884710375928968501259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1239846280501238624668345 929884710375928968501259)
              ·
                refine ⟨1394827065563893452751889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929884710375928968501259 1394827065563893452751889)
                ·
                  refine ⟨1046120299172920089563917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1394827065563893452751889 1046120299172920089563917)
                  ·
                    refine ⟨392295112189845033586469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1046120299172920089563917 392295112189845033586469)
                    ·
                      rfl

theorem cell22_1145988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_1145988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145988 prefixEnd_1145988 := by exact prefixLift 1145988
  have htrace : WordTrace (prefixWord ++ tailWord_1145988) baseStart_1145988 baseEnd_1145988 := by
    simpa [prefixWord, tailWord_1145988, baseEnd_1145988] using wordTrace_append hprefix tailTrace_1145988
  have hstable : (prefixWord ++ tailWord_1145988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145988).length < 2 ^ (prefixWord ++ tailWord_1145988).sum := by decide
  have hdescent : baseEnd_1145988 < baseStart_1145988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146016 : List Nat := [2, 1, 1, 4, 2, 1, 2, 5, 1, 3]
def baseStart_1146016 : Nat := 118140960795 + 1146016 * 2 ^ 59
def prefixEnd_1146016 : Nat := 4983230072969 + 3 ^ 40 * 1146016 * 2
def baseEnd_1146016 : Nat := 392304697162062293886383

theorem tailTrace_1146016 : CollatzResearch.WordTrace tailWord_1146016 prefixEnd_1146016 392304697162062293886383 := by
  unfold tailWord_1146016
  simp only [CollatzResearch.WordTrace]
  refine ⟨20899318708093615397764951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27865758277458153863686601 20899318708093615397764951)
  ·
    refine ⟨31348978062140423096647427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20899318708093615397764951 31348978062140423096647427)
    ·
      refine ⟨47023467093210634644971141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31348978062140423096647427 47023467093210634644971141)
      ·
        refine ⟨8816900079976993995932089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47023467093210634644971141 8816900079976993995932089)
        ·
          refine ⟨6612675059982745496949067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8816900079976993995932089 6612675059982745496949067)
          ·
            refine ⟨9919012589974118245423601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6612675059982745496949067 9919012589974118245423601)
            ·
              refine ⟨7439259442480588684067701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9919012589974118245423601 7439259442480588684067701)
              ·
                refine ⟨697430572732555189131347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7439259442480588684067701 697430572732555189131347)
                ·
                  refine ⟨1046145859098832783697021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 697430572732555189131347 1046145859098832783697021)
                  ·
                    refine ⟨392304697162062293886383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1046145859098832783697021 392304697162062293886383)
                    ·
                      rfl

theorem cell22_1146016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 1, 3].length) (baseStart_1146016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146016 prefixEnd_1146016 := by exact prefixLift 1146016
  have htrace : WordTrace (prefixWord ++ tailWord_1146016) baseStart_1146016 baseEnd_1146016 := by
    simpa [prefixWord, tailWord_1146016, baseEnd_1146016] using wordTrace_append hprefix tailTrace_1146016
  have hstable : (prefixWord ++ tailWord_1146016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146016).length < 2 ^ (prefixWord ++ tailWord_1146016).sum := by decide
  have hdescent : baseEnd_1146016 < baseStart_1146016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146033 : List Nat := [1, 2, 2, 5, 1, 2, 1, 4, 1, 3]
def baseStart_1146033 : Nat := 118140960795 + 1146033 * 2 ^ 59
def prefixEnd_1146033 : Nat := 4983230072969 + 3 ^ 40 * 1146033 * 2
def baseEnd_1146033 : Nat := 392310516609479916211331

theorem tailTrace_1146033 : CollatzResearch.WordTrace tailWord_1146033 prefixEnd_1146033 392310516609479916211331 := by
  unfold tailWord_1146033
  simp only [CollatzResearch.WordTrace]
  refine ⟨41799257457125642698898753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27866171638083761799265835 41799257457125642698898753)
  ·
    refine ⟨31349443092844232024174065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41799257457125642698898753 31349443092844232024174065)
    ·
      refine ⟨23512082319633174018130549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31349443092844232024174065 23512082319633174018130549)
      ·
        refine ⟨2204257717465610064199739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23512082319633174018130549 2204257717465610064199739)
        ·
          refine ⟨3306386576198415096299609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2204257717465610064199739 3306386576198415096299609)
          ·
            refine ⟨2479789932148811322224707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3306386576198415096299609 2479789932148811322224707)
            ·
              refine ⟨3719684898223216983337061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2479789932148811322224707 3719684898223216983337061)
              ·
                refine ⟨697440918416853184375699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3719684898223216983337061 697440918416853184375699)
                ·
                  refine ⟨1046161377625279776563549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 697440918416853184375699 1046161377625279776563549)
                  ·
                    refine ⟨392310516609479916211331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1046161377625279776563549 392310516609479916211331)
                    ·
                      rfl

theorem cell22_1146033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 1, 3].length) (baseStart_1146033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146033 prefixEnd_1146033 := by exact prefixLift 1146033
  have htrace : WordTrace (prefixWord ++ tailWord_1146033) baseStart_1146033 baseEnd_1146033 := by
    simpa [prefixWord, tailWord_1146033, baseEnd_1146033] using wordTrace_append hprefix tailTrace_1146033
  have hstable : (prefixWord ++ tailWord_1146033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146033).length < 2 ^ (prefixWord ++ tailWord_1146033).sum := by decide
  have hdescent : baseEnd_1146033 < baseStart_1146033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146044 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 2, 5]
def baseStart_1146044 : Nat := 118140960795 + 1146044 * 2 ^ 59
def prefixEnd_1146044 : Nat := 4983230072969 + 3 ^ 40 * 1146044 * 2
def baseEnd_1146044 : Nat := 392314282134279554186297

theorem tailTrace_1146044 : CollatzResearch.WordTrace tailWord_1146044 prefixEnd_1146044 392314282134279554186297 := by
  unfold tailWord_1146044
  simp only [CollatzResearch.WordTrace]
  refine ⟨20899829330042895788774593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27866439106723861051699457 20899829330042895788774593)
  ·
    refine ⟨15674871997532171841580945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20899829330042895788774593 15674871997532171841580945)
    ·
      refine ⟨11756153998149128881185709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15674871997532171841580945 11756153998149128881185709)
      ·
        refine ⟨4408557749305923330444641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11756153998149128881185709 4408557749305923330444641)
        ·
          refine ⟨3306418311979442497833481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4408557749305923330444641 3306418311979442497833481)
          ·
            refine ⟨2479813733984581873375111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3306418311979442497833481 2479813733984581873375111)
            ·
              refine ⟨3719720600976872810062667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2479813733984581873375111 3719720600976872810062667)
              ·
                refine ⟨5579580901465309215094001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3719720600976872810062667 5579580901465309215094001)
                ·
                  refine ⟨4184685676098981911320501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5579580901465309215094001 4184685676098981911320501)
                  ·
                    refine ⟨392314282134279554186297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4184685676098981911320501 392314282134279554186297)
                    ·
                      rfl

theorem cell22_1146044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_1146044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146044 prefixEnd_1146044 := by exact prefixLift 1146044
  have htrace : WordTrace (prefixWord ++ tailWord_1146044) baseStart_1146044 baseEnd_1146044 := by
    simpa [prefixWord, tailWord_1146044, baseEnd_1146044] using wordTrace_append hprefix tailTrace_1146044
  have hstable : (prefixWord ++ tailWord_1146044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146044).length < 2 ^ (prefixWord ++ tailWord_1146044).sum := by decide
  have hdescent : baseEnd_1146044 < baseStart_1146044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146050 : List Nat := [3, 5, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_1146050 : Nat := 118140960795 + 1146050 * 2 ^ 59
def prefixEnd_1146050 : Nat := 4983230072969 + 3 ^ 40 * 1146050 * 2
def baseEnd_1146050 : Nat := 392316336056897538536279

theorem tailTrace_1146050 : CollatzResearch.WordTrace tailWord_1146050 prefixEnd_1146050 392316336056897538536279 := by
  unfold tailWord_1146050
  simp only [CollatzResearch.WordTrace]
  refine ⟨10449969374516013650566901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27866584998709369734845069 10449969374516013650566901)
  ·
    refine ⟨979684628860876279740647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10449969374516013650566901 979684628860876279740647)
    ·
      refine ⟨1469526943291314419610971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 979684628860876279740647 1469526943291314419610971)
      ·
        refine ⟨2204290414936971629416457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1469526943291314419610971 2204290414936971629416457)
        ·
          refine ⟨1653217811202728722062343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2204290414936971629416457 1653217811202728722062343)
          ·
            refine ⟨2479826716804093083093515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1653217811202728722062343 2479826716804093083093515)
            ·
              refine ⟨3719740075206139624640273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2479826716804093083093515 3719740075206139624640273)
              ·
                refine ⟨2789805056404604718480205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3719740075206139624640273 2789805056404604718480205)
                ·
                  refine ⟨1046176896151726769430077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2789805056404604718480205 1046176896151726769430077)
                  ·
                    refine ⟨392316336056897538536279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1046176896151726769430077 392316336056897538536279)
                    ·
                      rfl

theorem cell22_1146050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_1146050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146050 prefixEnd_1146050 := by exact prefixLift 1146050
  have htrace : WordTrace (prefixWord ++ tailWord_1146050) baseStart_1146050 baseEnd_1146050 := by
    simpa [prefixWord, tailWord_1146050, baseEnd_1146050] using wordTrace_append hprefix tailTrace_1146050
  have hstable : (prefixWord ++ tailWord_1146050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146050).length < 2 ^ (prefixWord ++ tailWord_1146050).sum := by decide
  have hdescent : baseEnd_1146050 < baseStart_1146050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146117 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 2, 7]
def baseStart_1146117 : Nat := 118140960795 + 1146117 * 2 ^ 59
def prefixEnd_1146117 : Nat := 4983230072969 + 3 ^ 40 * 1146117 * 2
def baseEnd_1146117 : Nat := 392339271526131697111073

theorem tailTrace_1146117 : CollatzResearch.WordTrace tailWord_1146117 prefixEnd_1146117 392339271526131697111073 := by
  unfold tailWord_1146117
  simp only [CollatzResearch.WordTrace]
  refine ⟨41802321188821325044956605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27868214125880883363304403 41802321188821325044956605)
  ·
    refine ⟨15675870445807996891858727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41802321188821325044956605 15675870445807996891858727)
    ·
      refine ⟨23513805668711995337788091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15675870445807996891858727 23513805668711995337788091)
      ·
        refine ⟨35270708503067993006682137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23513805668711995337788091 35270708503067993006682137)
        ·
          refine ⟨26453031377300994755011603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35270708503067993006682137 26453031377300994755011603)
          ·
            refine ⟨39679547065951492132517405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26453031377300994755011603 39679547065951492132517405)
            ·
              refine ⟨14879830149731809549694027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39679547065951492132517405 14879830149731809549694027)
              ·
                refine ⟨22319745224597714324541041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14879830149731809549694027 22319745224597714324541041)
                ·
                  refine ⟨16739808918448285743405781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22319745224597714324541041 16739808918448285743405781)
                  ·
                    refine ⟨392339271526131697111073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16739808918448285743405781 392339271526131697111073)
                    ·
                      rfl

theorem cell22_1146117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_1146117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146117 prefixEnd_1146117 := by exact prefixLift 1146117
  have htrace : WordTrace (prefixWord ++ tailWord_1146117) baseStart_1146117 baseEnd_1146117 := by
    simpa [prefixWord, tailWord_1146117, baseEnd_1146117] using wordTrace_append hprefix tailTrace_1146117
  have hstable : (prefixWord ++ tailWord_1146117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146117).length < 2 ^ (prefixWord ++ tailWord_1146117).sum := by decide
  have hdescent : baseEnd_1146117 < baseStart_1146117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146142 : List Nat := [4, 3, 2, 1, 2, 1, 3, 2, 4]
def baseStart_1146142 : Nat := 118140960795 + 1146142 * 2 ^ 59
def prefixEnd_1146142 : Nat := 4983230072969 + 3 ^ 40 * 1146142 * 2
def baseEnd_1146142 : Nat := 130782609845679988411999

theorem tailTrace_1146142 : CollatzResearch.WordTrace tailWord_1146142 prefixEnd_1146142 130782609845679988411999 := by
  unfold tailWord_1146142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5225404126716344289327085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27868822009153836209744453 5225404126716344289327085)
  ·
    refine ⟨1959526547518629108497657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5225404126716344289327085 1959526547518629108497657)
    ·
      refine ⟨1469644910638971831373243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1959526547518629108497657 1469644910638971831373243)
      ·
        refine ⟨2204467365958457747059865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1469644910638971831373243 2204467365958457747059865)
        ·
          refine ⟨1653350524468843310294899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2204467365958457747059865 1653350524468843310294899)
          ·
            refine ⟨2480025786703264965442349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1653350524468843310294899 2480025786703264965442349)
            ·
              refine ⟨930009670013724362040881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2480025786703264965442349 930009670013724362040881)
              ·
                refine ⟨697507252510293271530661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 930009670013724362040881 697507252510293271530661)
                ·
                  refine ⟨130782609845679988411999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 697507252510293271530661 130782609845679988411999)
                  ·
                    rfl

theorem cell22_1146142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_1146142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146142 prefixEnd_1146142 := by exact prefixLift 1146142
  have htrace : WordTrace (prefixWord ++ tailWord_1146142) baseStart_1146142 baseEnd_1146142 := by
    simpa [prefixWord, tailWord_1146142, baseEnd_1146142] using wordTrace_append hprefix tailTrace_1146142
  have hstable : (prefixWord ++ tailWord_1146142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146142).length < 2 ^ (prefixWord ++ tailWord_1146142).sum := by decide
  have hdescent : baseEnd_1146142 < baseStart_1146142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146157 : List Nat := [1, 5, 3, 1, 1, 3, 2, 1, 2, 3]
def baseStart_1146157 : Nat := 118140960795 + 1146157 * 2 ^ 59
def prefixEnd_1146157 : Nat := 4983230072969 + 3 ^ 40 * 1146157 * 2
def baseEnd_1146157 : Nat := 392352964343584926110951

theorem tailTrace_1146157 : CollatzResearch.WordTrace tailWord_1146157 prefixEnd_1146157 392352964343584926110951 := by
  unfold tailWord_1146157
  simp only [CollatzResearch.WordTrace]
  refine ⟨41803780108676411876412725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27869186739117607917608483 41803780108676411876412725)
  ·
    refine ⟨3919104385188413613413693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41803780108676411876412725 3919104385188413613413693)
    ·
      refine ⟨1469664144445655105030135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3919104385188413613413693 1469664144445655105030135)
      ·
        refine ⟨2204496216668482657545203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1469664144445655105030135 2204496216668482657545203)
        ·
          refine ⟨3306744325002723986317805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2204496216668482657545203 3306744325002723986317805)
          ·
            refine ⟨1240029121876021494869177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3306744325002723986317805 1240029121876021494869177)
            ·
              refine ⟨930021841407016121151883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1240029121876021494869177 930021841407016121151883)
              ·
                refine ⟨1395032762110524181727825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 930021841407016121151883 1395032762110524181727825)
                ·
                  refine ⟨1046274571582893136295869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1395032762110524181727825 1046274571582893136295869)
                  ·
                    refine ⟨392352964343584926110951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1046274571582893136295869 392352964343584926110951)
                    ·
                      rfl

theorem cell22_1146157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_1146157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146157 prefixEnd_1146157 := by exact prefixLift 1146157
  have htrace : WordTrace (prefixWord ++ tailWord_1146157) baseStart_1146157 baseEnd_1146157 := by
    simpa [prefixWord, tailWord_1146157, baseEnd_1146157] using wordTrace_append hprefix tailTrace_1146157
  have hstable : (prefixWord ++ tailWord_1146157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146157).length < 2 ^ (prefixWord ++ tailWord_1146157).sum := by decide
  have hdescent : baseEnd_1146157 < baseStart_1146157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146243 : List Nat := [1, 1, 1, 3, 5, 2, 2, 3, 4]
def baseStart_1146243 : Nat := 118140960795 + 1146243 * 2 ^ 59
def prefixEnd_1146243 : Nat := 4983230072969 + 3 ^ 40 * 1146243 * 2
def baseEnd_1146243 : Nat := 130794134633703122820229

theorem tailTrace_1146243 : CollatzResearch.WordTrace tailWord_1146243 prefixEnd_1146243 130794134633703122820229 := by
  unfold tailWord_1146243
  simp only [CollatzResearch.WordTrace]
  refine ⟨41806916786364848564043383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27871277857576565709362255 41806916786364848564043383)
  ·
    refine ⟨62710375179547272846065075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41806916786364848564043383 62710375179547272846065075)
    ·
      refine ⟨94065562769320909269097613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62710375179547272846065075 94065562769320909269097613)
      ·
        refine ⟨35274586038495340975911605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94065562769320909269097613 35274586038495340975911605)
        ·
          refine ⟨3306992441108938216491713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35274586038495340975911605 3306992441108938216491713)
          ·
            refine ⟨2480244330831703662368785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3306992441108938216491713 2480244330831703662368785)
            ·
              refine ⟨1860183248123777746776589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2480244330831703662368785 1860183248123777746776589)
              ·
                refine ⟨697568718046416655041221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1860183248123777746776589 697568718046416655041221)
                ·
                  refine ⟨130794134633703122820229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 697568718046416655041221 130794134633703122820229)
                  ·
                    rfl

theorem cell22_1146243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 4].length) (baseStart_1146243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146243 prefixEnd_1146243 := by exact prefixLift 1146243
  have htrace : WordTrace (prefixWord ++ tailWord_1146243) baseStart_1146243 baseEnd_1146243 := by
    simpa [prefixWord, tailWord_1146243, baseEnd_1146243] using wordTrace_append hprefix tailTrace_1146243
  have hstable : (prefixWord ++ tailWord_1146243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146243).length < 2 ^ (prefixWord ++ tailWord_1146243).sum := by decide
  have hdescent : baseEnd_1146243 < baseStart_1146243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146284 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 2, 6]
def baseStart_1146284 : Nat := 118140960795 + 1146284 * 2 ^ 59
def prefixEnd_1146284 : Nat := 4983230072969 + 3 ^ 40 * 1146284 * 2
def baseEnd_1146284 : Nat := 392396439038998928185561

theorem tailTrace_1146284 : CollatzResearch.WordTrace tailWord_1146284 prefixEnd_1146284 392396439038998928185561 := by
  unfold tailWord_1146284
  simp only [CollatzResearch.WordTrace]
  refine ⟨20904206089608156283142953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27872274786144208377523937 20904206089608156283142953)
  ·
    refine ⟨15678154567206117212357215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20904206089608156283142953 15678154567206117212357215)
    ·
      refine ⟨23517231850809175818535823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15678154567206117212357215 23517231850809175818535823)
      ·
        refine ⟨35275847776213763727803735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23517231850809175818535823 35275847776213763727803735)
        ·
          refine ⟨52913771664320645591705603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35275847776213763727803735 52913771664320645591705603)
          ·
            refine ⟨79370657496480968387558405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52913771664320645591705603 79370657496480968387558405)
            ·
              refine ⟨14881998280590181572667201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79370657496480968387558405 14881998280590181572667201)
              ·
                refine ⟨11161498710442636179500401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14881998280590181572667201 11161498710442636179500401)
                ·
                  refine ⟨8371124032831977134625301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11161498710442636179500401 8371124032831977134625301)
                  ·
                    refine ⟨392396439038998928185561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8371124032831977134625301 392396439038998928185561)
                    ·
                      rfl

theorem cell22_1146284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_1146284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146284 prefixEnd_1146284 := by exact prefixLift 1146284
  have htrace : WordTrace (prefixWord ++ tailWord_1146284) baseStart_1146284 baseEnd_1146284 := by
    simpa [prefixWord, tailWord_1146284, baseEnd_1146284] using wordTrace_append hprefix tailTrace_1146284
  have hstable : (prefixWord ++ tailWord_1146284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146284).length < 2 ^ (prefixWord ++ tailWord_1146284).sum := by decide
  have hdescent : baseEnd_1146284 < baseStart_1146284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146316 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 7]
def baseStart_1146316 : Nat := 118140960795 + 1146316 * 2 ^ 59
def prefixEnd_1146316 : Nat := 4983230072969 + 3 ^ 40 * 1146316 * 2
def baseEnd_1146316 : Nat := 130802464430987170461821

theorem tailTrace_1146316 : CollatzResearch.WordTrace tailWord_1146316 prefixEnd_1146316 130802464430987170461821 := by
  unfold tailWord_1146316
  simp only [CollatzResearch.WordTrace]
  refine ⟨20904789657550191015725401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27873052876733588020967201 20904789657550191015725401)
  ·
    refine ⟨15678592243162643261794051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20904789657550191015725401 15678592243162643261794051)
    ·
      refine ⟨23517888364743964892691077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15678592243162643261794051 23517888364743964892691077)
      ·
        refine ⟨4409604068389493417379577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23517888364743964892691077 4409604068389493417379577)
        ·
          refine ⟨3307203051292120063034683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4409604068389493417379577 3307203051292120063034683)
          ·
            refine ⟨4960804576938180094552025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3307203051292120063034683 4960804576938180094552025)
            ·
              refine ⟨3720603432703635070914019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4960804576938180094552025 3720603432703635070914019)
              ·
                refine ⟨5580905149055452606371029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3720603432703635070914019 5580905149055452606371029)
                ·
                  refine ⟨130802464430987170461821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5580905149055452606371029 130802464430987170461821)
                  ·
                    rfl

theorem cell22_1146316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_1146316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146316 prefixEnd_1146316 := by exact prefixLift 1146316
  have htrace : WordTrace (prefixWord ++ tailWord_1146316) baseStart_1146316 baseEnd_1146316 := by
    simpa [prefixWord, tailWord_1146316, baseEnd_1146316] using wordTrace_append hprefix tailTrace_1146316
  have hstable : (prefixWord ++ tailWord_1146316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146316).length < 2 ^ (prefixWord ++ tailWord_1146316).sum := by decide
  have hdescent : baseEnd_1146316 < baseStart_1146316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146333 : List Nat := [1, 4, 3, 1, 1, 3, 1, 3, 5]
def baseStart_1146333 : Nat := 118140960795 + 1146333 * 2 ^ 59
def prefixEnd_1146333 : Nat := 4983230072969 + 3 ^ 40 * 1146333 * 2
def baseEnd_1146333 : Nat := 130804404246793044570137

theorem tailTrace_1146333 : CollatzResearch.WordTrace tailWord_1146333 prefixEnd_1146333 130804404246793044570137 := by
  unfold tailWord_1146333
  simp only [CollatzResearch.WordTrace]
  refine ⟨41810199356038793934819653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27873466237359195956546435 41810199356038793934819653)
  ·
    refine ⟨7839412379257273862778685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41810199356038793934819653 7839412379257273862778685)
    ·
      refine ⟨2939779642221477698542007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7839412379257273862778685 2939779642221477698542007)
      ·
        refine ⟨4409669463332216547813011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2939779642221477698542007 4409669463332216547813011)
        ·
          refine ⟨6614504194998324821719517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4409669463332216547813011 6614504194998324821719517)
          ·
            refine ⟨2480439073124371808144819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6614504194998324821719517 2480439073124371808144819)
            ·
              refine ⟨3720658609686557712217229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2480439073124371808144819 3720658609686557712217229)
              ·
                refine ⟨1395246978632459142081461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3720658609686557712217229 1395246978632459142081461)
                ·
                  refine ⟨130804404246793044570137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1395246978632459142081461 130804404246793044570137)
                  ·
                    rfl

theorem cell22_1146333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_1146333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146333 prefixEnd_1146333 := by exact prefixLift 1146333
  have htrace : WordTrace (prefixWord ++ tailWord_1146333) baseStart_1146333 baseEnd_1146333 := by
    simpa [prefixWord, tailWord_1146333, baseEnd_1146333] using wordTrace_append hprefix tailTrace_1146333
  have hstable : (prefixWord ++ tailWord_1146333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146333).length < 2 ^ (prefixWord ++ tailWord_1146333).sum := by decide
  have hdescent : baseEnd_1146333 < baseStart_1146333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146528 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 3, 5]
def baseStart_1146528 : Nat := 118140960795 + 1146528 * 2 ^ 59
def prefixEnd_1146528 : Nat := 4983230072969 + 3 ^ 40 * 1146528 * 2
def baseEnd_1146528 : Nat := 392479965225463625084813

theorem tailTrace_1146528 : CollatzResearch.WordTrace tailWord_1146528 prefixEnd_1146528 392479965225463625084813 := by
  unfold tailWord_1146528
  simp only [CollatzResearch.WordTrace]
  refine ⟨20908655795166171119084119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27878207726888228158778825 20908655795166171119084119)
  ·
    refine ⟨31362983692749256678626179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20908655795166171119084119 31362983692749256678626179)
    ·
      refine ⟨47044475539123885017939269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31362983692749256678626179 47044475539123885017939269)
      ·
        refine ⟨8820839163585728440863613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47044475539123885017939269 8820839163585728440863613)
        ·
          refine ⟨3307814686344648165323855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8820839163585728440863613 3307814686344648165323855)
          ·
            refine ⟨4961722029516972247985783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3307814686344648165323855 4961722029516972247985783)
            ·
              refine ⟨7442583044275458371978675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4961722029516972247985783 7442583044275458371978675)
              ·
                refine ⟨11163874566413187557968013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7442583044275458371978675 11163874566413187557968013)
                ·
                  refine ⟨4186452962404945334238005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11163874566413187557968013 4186452962404945334238005)
                  ·
                    refine ⟨392479965225463625084813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4186452962404945334238005 392479965225463625084813)
                    ·
                      rfl

theorem cell22_1146528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_1146528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146528 prefixEnd_1146528 := by exact prefixLift 1146528
  have htrace : WordTrace (prefixWord ++ tailWord_1146528) baseStart_1146528 baseEnd_1146528 := by
    simpa [prefixWord, tailWord_1146528, baseEnd_1146528] using wordTrace_append hprefix tailTrace_1146528
  have hstable : (prefixWord ++ tailWord_1146528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146528).length < 2 ^ (prefixWord ++ tailWord_1146528).sum := by decide
  have hdescent : baseEnd_1146528 < baseStart_1146528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146532 : List Nat := [2, 3, 1, 2, 2, 3, 3, 1, 1, 4]
def baseStart_1146532 : Nat := 118140960795 + 1146532 * 2 ^ 59
def prefixEnd_1146532 : Nat := 4983230072969 + 3 ^ 40 * 1146532 * 2
def baseEnd_1146532 : Nat := 392481334507208947984801

theorem tailTrace_1146532 : CollatzResearch.WordTrace tailWord_1146532 prefixEnd_1146532 392481334507208947984801 := by
  unfold tailWord_1146532
  simp only [CollatzResearch.WordTrace]
  refine ⟨20908728741158925460656925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27878304988211900614209233 20908728741158925460656925)
  ·
    refine ⟨7840773277934597047746347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20908728741158925460656925 7840773277934597047746347)
    ·
      refine ⟨11761159916901895571619521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7840773277934597047746347 11761159916901895571619521)
      ·
        refine ⟨8820869937676421678714641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11761159916901895571619521 8820869937676421678714641)
        ·
          refine ⟨6615652453257316259035981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8820869937676421678714641 6615652453257316259035981)
          ·
            refine ⟨2480869669971493597138493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6615652453257316259035981 2480869669971493597138493)
            ·
              refine ⟨930326126239310098926935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2480869669971493597138493 930326126239310098926935)
              ·
                refine ⟨1395489189358965148390403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 930326126239310098926935 1395489189358965148390403)
                ·
                  refine ⟨2093233784038447722585605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1395489189358965148390403 2093233784038447722585605)
                  ·
                    refine ⟨392481334507208947984801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2093233784038447722585605 392481334507208947984801)
                    ·
                      rfl

theorem cell22_1146532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_1146532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146532 prefixEnd_1146532 := by exact prefixLift 1146532
  have htrace : WordTrace (prefixWord ++ tailWord_1146532) baseStart_1146532 baseEnd_1146532 := by
    simpa [prefixWord, tailWord_1146532, baseEnd_1146532] using wordTrace_append hprefix tailTrace_1146532
  have hstable : (prefixWord ++ tailWord_1146532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146532).length < 2 ^ (prefixWord ++ tailWord_1146532).sum := by decide
  have hdescent : baseEnd_1146532 < baseStart_1146532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146543 : List Nat := [1, 1, 2, 1, 2, 4, 1, 4, 2, 4]
def baseStart_1146543 : Nat := 118140960795 + 1146543 * 2 ^ 59
def prefixEnd_1146543 : Nat := 4983230072969 + 3 ^ 40 * 1146543 * 2
def baseEnd_1146543 : Nat := 392485100032008585959767

theorem tailTrace_1146543 : CollatzResearch.WordTrace tailWord_1146543 prefixEnd_1146543 392485100032008585959767 := by
  unfold tailWord_1146543
  simp only [CollatzResearch.WordTrace]
  refine ⟨41817858685277999799964283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27878572456851999866642855 41817858685277999799964283)
  ·
    refine ⟨62726788027916999699946425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41817858685277999799964283 62726788027916999699946425)
    ·
      refine ⟨47045091020937749774959819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62726788027916999699946425 47045091020937749774959819)
      ·
        refine ⟨70567636531406624662439729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47045091020937749774959819 70567636531406624662439729)
        ·
          refine ⟨52925727398554968496829797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70567636531406624662439729 52925727398554968496829797)
          ·
            refine ⟨9923573887229056593155587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52925727398554968496829797 9923573887229056593155587)
            ·
              refine ⟨14885360830843584889733381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9923573887229056593155587 14885360830843584889733381)
              ·
                refine ⟨2791005155783172166825009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14885360830843584889733381 2791005155783172166825009)
                ·
                  refine ⟨2093253866837379125118757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2791005155783172166825009 2093253866837379125118757)
                  ·
                    refine ⟨392485100032008585959767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2093253866837379125118757 392485100032008585959767)
                    ·
                      rfl

theorem cell22_1146543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 4].length) (baseStart_1146543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146543 prefixEnd_1146543 := by exact prefixLift 1146543
  have htrace : WordTrace (prefixWord ++ tailWord_1146543) baseStart_1146543 baseEnd_1146543 := by
    simpa [prefixWord, tailWord_1146543, baseEnd_1146543] using wordTrace_append hprefix tailTrace_1146543
  have hstable : (prefixWord ++ tailWord_1146543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146543).length < 2 ^ (prefixWord ++ tailWord_1146543).sum := by decide
  have hdescent : baseEnd_1146543 < baseStart_1146543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146607 : List Nat := [1, 1, 2, 1, 5, 1, 1, 6, 1, 3]
def baseStart_1146607 : Nat := 118140960795 + 1146607 * 2 ^ 59
def prefixEnd_1146607 : Nat := 4983230072969 + 3 ^ 40 * 1146607 * 2
def baseEnd_1146607 : Nat := 392507008539933752359571

theorem tailTrace_1146607 : CollatzResearch.WordTrace tailWord_1146607 prefixEnd_1146607 392507008539933752359571 := by
  unfold tailWord_1146607
  simp only [CollatzResearch.WordTrace]
  refine ⟨41820192957046138730294075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27880128638030759153529383 41820192957046138730294075)
  ·
    refine ⟨62730289435569208095441113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41820192957046138730294075 62730289435569208095441113)
    ·
      refine ⟨47047717076676906071580835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62730289435569208095441113 47047717076676906071580835)
      ·
        refine ⟨70571575615015359107371253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47047717076676906071580835 70571575615015359107371253)
        ·
          refine ⟨6616085213907689916316055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70571575615015359107371253 6616085213907689916316055)
          ·
            refine ⟨9924127820861534874474083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6616085213907689916316055 9924127820861534874474083)
            ·
              refine ⟨14886191731292302311711125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9924127820861534874474083 14886191731292302311711125)
              ·
                refine ⟨697790237404326670861459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14886191731292302311711125 697790237404326670861459)
                ·
                  refine ⟨1046685356106490006292189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 697790237404326670861459 1046685356106490006292189)
                  ·
                    refine ⟨392507008539933752359571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1046685356106490006292189 392507008539933752359571)
                    ·
                      rfl

theorem cell22_1146607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 1, 3].length) (baseStart_1146607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146607 prefixEnd_1146607 := by exact prefixLift 1146607
  have htrace : WordTrace (prefixWord ++ tailWord_1146607) baseStart_1146607 baseEnd_1146607 := by
    simpa [prefixWord, tailWord_1146607, baseEnd_1146607] using wordTrace_append hprefix tailTrace_1146607
  have hstable : (prefixWord ++ tailWord_1146607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146607).length < 2 ^ (prefixWord ++ tailWord_1146607).sum := by decide
  have hdescent : baseEnd_1146607 < baseStart_1146607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146648 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 8]
def baseStart_1146648 : Nat := 118140960795 + 1146648 * 2 ^ 59
def prefixEnd_1146648 : Nat := 4983230072969 + 3 ^ 40 * 1146648 * 2
def baseEnd_1146648 : Nat := 130840347892607770694815

theorem tailTrace_1146648 : CollatzResearch.WordTrace tailWord_1146648 prefixEnd_1146648 130840347892607770694815 := by
  unfold tailWord_1146648
  simp only [CollatzResearch.WordTrace]
  refine ⟨20910844174948801366268299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27881125566598401821691065 20910844174948801366268299)
  ·
    refine ⟨31366266262423202049402449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20910844174948801366268299 31366266262423202049402449)
    ·
      refine ⟨23524699696817401537051837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31366266262423202049402449 23524699696817401537051837)
      ·
        refine ⟨8821762386306525576394439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23524699696817401537051837 8821762386306525576394439)
        ·
          refine ⟨13232643579459788364591659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8821762386306525576394439 13232643579459788364591659)
          ·
            refine ⟨19848965369189682546887489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13232643579459788364591659 19848965369189682546887489)
            ·
              refine ⟨14886724026892261910165617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19848965369189682546887489 14886724026892261910165617)
              ·
                refine ⟨11165043020169196432624213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14886724026892261910165617 11165043020169196432624213)
                ·
                  refine ⟨130840347892607770694815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11165043020169196432624213 130840347892607770694815)
                  ·
                    rfl

theorem cell22_1146648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 8].length) (baseStart_1146648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146648 prefixEnd_1146648 := by exact prefixLift 1146648
  have htrace : WordTrace (prefixWord ++ tailWord_1146648) baseStart_1146648 baseEnd_1146648 := by
    simpa [prefixWord, tailWord_1146648, baseEnd_1146648] using wordTrace_append hprefix tailTrace_1146648
  have hstable : (prefixWord ++ tailWord_1146648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146648).length < 2 ^ (prefixWord ++ tailWord_1146648).sum := by decide
  have hdescent : baseEnd_1146648 < baseStart_1146648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146693 : List Nat := [1, 3, 1, 1, 1, 2, 3, 10]
def baseStart_1146693 : Nat := 118140960795 + 1146693 * 2 ^ 59
def prefixEnd_1146693 : Nat := 4983230072969 + 3 ^ 40 * 1146693 * 2
def baseEnd_1146693 : Nat := 43615160899717577189923

theorem tailTrace_1146693 : CollatzResearch.WordTrace tailWord_1146693 prefixEnd_1146693 43615160899717577189923 := by
  unfold tailWord_1146693
  simp only [CollatzResearch.WordTrace]
  refine ⟨41823329634734575417924733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27882219756489716945283155 41823329634734575417924733)
  ·
    refine ⟨15683748613025465781721775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41823329634734575417924733 15683748613025465781721775)
    ·
      refine ⟨23525622919538198672582663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15683748613025465781721775 23525622919538198672582663)
      ·
        refine ⟨35288434379307298008873995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23525622919538198672582663 35288434379307298008873995)
        ·
          refine ⟨52932651568960947013310993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35288434379307298008873995 52932651568960947013310993)
          ·
            refine ⟨39699488676720710259983245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52932651568960947013310993 39699488676720710259983245)
            ·
              refine ⟨14887308253770266347493717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39699488676720710259983245 14887308253770266347493717)
              ·
                refine ⟨43615160899717577189923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14887308253770266347493717 43615160899717577189923)
                ·
                  rfl

theorem cell22_1146693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 10].length) (baseStart_1146693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146693 prefixEnd_1146693 := by exact prefixLift 1146693
  have htrace : WordTrace (prefixWord ++ tailWord_1146693) baseStart_1146693 baseEnd_1146693 := by
    simpa [prefixWord, tailWord_1146693, baseEnd_1146693] using wordTrace_append hprefix tailTrace_1146693
  have hstable : (prefixWord ++ tailWord_1146693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146693).length < 2 ^ (prefixWord ++ tailWord_1146693).sum := by decide
  have hdescent : baseEnd_1146693 < baseStart_1146693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146695 : List Nat := [1, 1, 4, 1, 2, 1, 3, 3, 2, 4]
def baseStart_1146695 : Nat := 118140960795 + 1146695 * 2 ^ 59
def prefixEnd_1146695 : Nat := 4983230072969 + 3 ^ 40 * 1146695 * 2
def baseEnd_1146695 : Nat := 392537132738330856159301

theorem tailTrace_1146695 : CollatzResearch.WordTrace tailWord_1146695 prefixEnd_1146695 392537132738330856159301 := by
  unfold tailWord_1146695
  simp only [CollatzResearch.WordTrace]
  refine ⟨41823402580727329759497539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27882268387151553172998359 41823402580727329759497539)
  ·
    refine ⟨62735103871090994639246309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41823402580727329759497539 62735103871090994639246309)
    ·
      refine ⟨11762831975829561494858683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62735103871090994639246309 11762831975829561494858683)
      ·
        refine ⟨17644247963744342242288025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11762831975829561494858683 17644247963744342242288025)
        ·
          refine ⟨13233185972808256681716019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17644247963744342242288025 13233185972808256681716019)
          ·
            refine ⟨19849778959212385022574029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13233185972808256681716019 19849778959212385022574029)
            ·
              refine ⟨7443667109704644383465261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19849778959212385022574029 7443667109704644383465261)
              ·
                refine ⟨2791375166139241643799473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7443667109704644383465261 2791375166139241643799473)
                ·
                  refine ⟨2093531374604431232849605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2791375166139241643799473 2093531374604431232849605)
                  ·
                    refine ⟨392537132738330856159301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2093531374604431232849605 392537132738330856159301)
                    ·
                      rfl

theorem cell22_1146695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_1146695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146695 prefixEnd_1146695 := by exact prefixLift 1146695
  have htrace : WordTrace (prefixWord ++ tailWord_1146695) baseStart_1146695 baseEnd_1146695 := by
    simpa [prefixWord, tailWord_1146695, baseEnd_1146695] using wordTrace_append hprefix tailTrace_1146695
  have hstable : (prefixWord ++ tailWord_1146695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146695).length < 2 ^ (prefixWord ++ tailWord_1146695).sum := by decide
  have hdescent : baseEnd_1146695 < baseStart_1146695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146701 : List Nat := [1, 6, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_1146701 : Nat := 118140960795 + 1146701 * 2 ^ 59
def prefixEnd_1146701 : Nat := 4983230072969 + 3 ^ 40 * 1146701 * 2
def baseEnd_1146701 : Nat := 392539186660948840509283

theorem tailTrace_1146701 : CollatzResearch.WordTrace tailWord_1146701 prefixEnd_1146701 392539186660948840509283 := by
  unfold tailWord_1146701
  simp only [CollatzResearch.WordTrace]
  refine ⟨41823621418705592784215957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27882414279137061856143971 41823621418705592784215957)
  ·
    refine ⟨1960482254001824661760123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41823621418705592784215957 1960482254001824661760123)
    ·
      refine ⟨2940723381002736992640185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1960482254001824661760123 2940723381002736992640185)
      ·
        refine ⟨2205542535752052744480139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2940723381002736992640185 2205542535752052744480139)
        ·
          refine ⟨3308313803628079116720209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2205542535752052744480139 3308313803628079116720209)
          ·
            refine ⟨2481235352721059337540157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3308313803628079116720209 2481235352721059337540157)
            ·
              refine ⟨930463257270397251577559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2481235352721059337540157 930463257270397251577559)
              ·
                refine ⟨1395694885905595877366339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 930463257270397251577559 1395694885905595877366339)
                ·
                  refine ⟨2093542328858393816049509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1395694885905595877366339 2093542328858393816049509)
                  ·
                    refine ⟨392539186660948840509283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2093542328858393816049509 392539186660948840509283)
                    ·
                      rfl

theorem cell22_1146701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_1146701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146701 prefixEnd_1146701 := by exact prefixLift 1146701
  have htrace : WordTrace (prefixWord ++ tailWord_1146701) baseStart_1146701 baseEnd_1146701 := by
    simpa [prefixWord, tailWord_1146701, baseEnd_1146701] using wordTrace_append hprefix tailTrace_1146701
  have hstable : (prefixWord ++ tailWord_1146701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146701).length < 2 ^ (prefixWord ++ tailWord_1146701).sum := by decide
  have hdescent : baseEnd_1146701 < baseStart_1146701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146772 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 7]
def baseStart_1146772 : Nat := 118140960795 + 1146772 * 2 ^ 59
def prefixEnd_1146772 : Nat := 4983230072969 + 3 ^ 40 * 1146772 * 2
def baseEnd_1146772 : Nat := 130854497137309440661355

theorem tailTrace_1146772 : CollatzResearch.WordTrace tailWord_1146772 prefixEnd_1146772 130854497137309440661355 := by
  unfold tailWord_1146772
  simp only [CollatzResearch.WordTrace]
  refine ⟨20913105500724185955025285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27884140667632247940033713 20913105500724185955025285)
  ·
    refine ⟨3921207281385784866567241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20913105500724185955025285 3921207281385784866567241)
    ·
      refine ⟨2940905461039338649925431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3921207281385784866567241 2940905461039338649925431)
      ·
        refine ⟨4411358191559007974888147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2940905461039338649925431 4411358191559007974888147)
        ·
          refine ⟨6617037287338511962332221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4411358191559007974888147 6617037287338511962332221)
          ·
            refine ⟨2481388982751941985874583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6617037287338511962332221 2481388982751941985874583)
            ·
              refine ⟨3722083474127912978811875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2481388982751941985874583 3722083474127912978811875)
              ·
                refine ⟨5583125211191869468217813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3722083474127912978811875 5583125211191869468217813)
                ·
                  refine ⟨130854497137309440661355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5583125211191869468217813 130854497137309440661355)
                  ·
                    rfl

theorem cell22_1146772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_1146772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146772 prefixEnd_1146772 := by exact prefixLift 1146772
  have htrace : WordTrace (prefixWord ++ tailWord_1146772) baseStart_1146772 baseEnd_1146772 := by
    simpa [prefixWord, tailWord_1146772, baseEnd_1146772] using wordTrace_append hprefix tailTrace_1146772
  have hstable : (prefixWord ++ tailWord_1146772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146772).length < 2 ^ (prefixWord ++ tailWord_1146772).sum := by decide
  have hdescent : baseEnd_1146772 < baseStart_1146772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146776 : List Nat := [2, 1, 2, 6, 1, 1, 2, 1, 3, 3]
def baseStart_1146776 : Nat := 118140960795 + 1146776 * 2 ^ 59
def prefixEnd_1146776 : Nat := 4983230072969 + 3 ^ 40 * 1146776 * 2
def baseEnd_1146776 : Nat := 392564860693673644884053

theorem tailTrace_1146776 : CollatzResearch.WordTrace tailWord_1146776 prefixEnd_1146776 392564860693673644884053 := by
  unfold tailWord_1146776
  simp only [CollatzResearch.WordTrace]
  refine ⟨20913178446716940296598091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27884237928955920395464121 20913178446716940296598091)
  ·
    refine ⟨31369767670075410444897137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20913178446716940296598091 31369767670075410444897137)
    ·
      refine ⟨23527325752556557833672853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31369767670075410444897137 23527325752556557833672853)
      ·
        refine ⟨1102843394651088648453415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23527325752556557833672853 1102843394651088648453415)
        ·
          refine ⟨1654265091976632972680123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1102843394651088648453415 1654265091976632972680123)
          ·
            refine ⟨2481397637964949459020185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1654265091976632972680123 2481397637964949459020185)
            ·
              refine ⟨1861048228473712094265139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2481397637964949459020185 1861048228473712094265139)
              ·
                refine ⟨2791572342710568141397709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1861048228473712094265139 2791572342710568141397709)
                ·
                  refine ⟨1046839628516463053024141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2791572342710568141397709 1046839628516463053024141)
                  ·
                    refine ⟨392564860693673644884053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1046839628516463053024141 392564860693673644884053)
                    ·
                      rfl

theorem cell22_1146776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_1146776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146776 prefixEnd_1146776 := by exact prefixLift 1146776
  have htrace : WordTrace (prefixWord ++ tailWord_1146776) baseStart_1146776 baseEnd_1146776 := by
    simpa [prefixWord, tailWord_1146776, baseEnd_1146776] using wordTrace_append hprefix tailTrace_1146776
  have hstable : (prefixWord ++ tailWord_1146776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146776).length < 2 ^ (prefixWord ++ tailWord_1146776).sum := by decide
  have hdescent : baseEnd_1146776 < baseStart_1146776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146815 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 3, 5]
def baseStart_1146815 : Nat := 118140960795 + 1146815 * 2 ^ 59
def prefixEnd_1146815 : Nat := 4983230072969 + 3 ^ 40 * 1146815 * 2
def baseEnd_1146815 : Nat := 392578211190690543158933

theorem tailTrace_1146815 : CollatzResearch.WordTrace tailWord_1146815 prefixEnd_1146815 392578211190690543158933 := by
  unfold tailWord_1146815
  simp only [CollatzResearch.WordTrace]
  refine ⟨41827779340292590253865899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27885186226861726835910599 41827779340292590253865899)
  ·
    refine ⟨62741669010438885380798849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41827779340292590253865899 62741669010438885380798849)
    ·
      refine ⟨47056251757829164035599137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62741669010438885380798849 47056251757829164035599137)
      ·
        refine ⟨35292188818371873026699353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47056251757829164035599137 35292188818371873026699353)
        ·
          refine ⟨26469141613778904770024515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35292188818371873026699353 26469141613778904770024515)
          ·
            refine ⟨39703712420668357155036773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26469141613778904770024515 39703712420668357155036773)
            ·
              refine ⟨7444446078875316966569395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39703712420668357155036773 7444446078875316966569395)
              ·
                refine ⟨11166669118312975449854093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7444446078875316966569395 11166669118312975449854093)
                ·
                  refine ⟨4187500919367365793695285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11166669118312975449854093 4187500919367365793695285)
                  ·
                    refine ⟨392578211190690543158933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4187500919367365793695285 392578211190690543158933)
                    ·
                      rfl

theorem cell22_1146815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_1146815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146815 prefixEnd_1146815 := by exact prefixLift 1146815
  have htrace : WordTrace (prefixWord ++ tailWord_1146815) baseStart_1146815 baseEnd_1146815 := by
    simpa [prefixWord, tailWord_1146815, baseEnd_1146815] using wordTrace_append hprefix tailTrace_1146815
  have hstable : (prefixWord ++ tailWord_1146815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146815).length < 2 ^ (prefixWord ++ tailWord_1146815).sum := by decide
  have hdescent : baseEnd_1146815 < baseStart_1146815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146832 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 4, 3]
def baseStart_1146832 : Nat := 118140960795 + 1146832 * 2 ^ 59
def prefixEnd_1146832 : Nat := 4983230072969 + 3 ^ 40 * 1146832 * 2
def baseEnd_1146832 : Nat := 392584030638108165483881

theorem tailTrace_1146832 : CollatzResearch.WordTrace tailWord_1146832 prefixEnd_1146832 392584030638108165483881 := by
  unfold tailWord_1146832
  simp only [CollatzResearch.WordTrace]
  refine ⟨20914199690615501078617375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27885599587487334771489833 20914199690615501078617375)
  ·
    refine ⟨31371299535923251617926063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20914199690615501078617375 31371299535923251617926063)
    ·
      refine ⟨47056949303884877426889095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31371299535923251617926063 47056949303884877426889095)
      ·
        refine ⟨70585423955827316140333643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47056949303884877426889095 70585423955827316140333643)
        ·
          refine ⟨105878135933740974210500465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70585423955827316140333643 105878135933740974210500465)
          ·
            refine ⟨79408601950305730657875349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105878135933740974210500465 79408601950305730657875349)
            ·
              refine ⟨3722278216420581124587907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79408601950305730657875349 3722278216420581124587907)
              ·
                refine ⟨5583417324630871686881861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3722278216420581124587907 5583417324630871686881861)
                ·
                  refine ⟨1046890748368288441290349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5583417324630871686881861 1046890748368288441290349)
                  ·
                    refine ⟨392584030638108165483881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1046890748368288441290349 392584030638108165483881)
                    ·
                      rfl

theorem cell22_1146832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 4, 3].length) (baseStart_1146832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146832 prefixEnd_1146832 := by exact prefixLift 1146832
  have htrace : WordTrace (prefixWord ++ tailWord_1146832) baseStart_1146832 baseEnd_1146832 := by
    simpa [prefixWord, tailWord_1146832, baseEnd_1146832] using wordTrace_append hprefix tailTrace_1146832
  have hstable : (prefixWord ++ tailWord_1146832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146832).length < 2 ^ (prefixWord ++ tailWord_1146832).sum := by decide
  have hdescent : baseEnd_1146832 < baseStart_1146832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146860 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 2, 7]
def baseStart_1146860 : Nat := 118140960795 + 1146860 * 2 ^ 59
def prefixEnd_1146860 : Nat := 4983230072969 + 3 ^ 40 * 1146860 * 2
def baseEnd_1146860 : Nat := 392593615610325425783795

theorem tailTrace_1146860 : CollatzResearch.WordTrace tailWord_1146860 prefixEnd_1146860 392593615610325425783795 := by
  unfold tailWord_1146860
  simp only [CollatzResearch.WordTrace]
  refine ⟨20914710312564781469627017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27886280416753041959502689 20914710312564781469627017)
  ·
    refine ⟨15686032734423586102220263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20914710312564781469627017 15686032734423586102220263)
    ·
      refine ⟨23529049101635379153330395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15686032734423586102220263 23529049101635379153330395)
      ·
        refine ⟨35293573652453068729995593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23529049101635379153330395 35293573652453068729995593)
        ·
          refine ⟨26470180239339801547496695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35293573652453068729995593 26470180239339801547496695)
          ·
            refine ⟨39705270359009702321245043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26470180239339801547496695 39705270359009702321245043)
            ·
              refine ⟨59557905538514553481867565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39705270359009702321245043 59557905538514553481867565)
              ·
                refine ⟨22334214576942957555700337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59557905538514553481867565 22334214576942957555700337)
                ·
                  refine ⟨16750660932707218166775253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22334214576942957555700337 16750660932707218166775253)
                  ·
                    refine ⟨392593615610325425783795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16750660932707218166775253 392593615610325425783795)
                    ·
                      rfl

theorem cell22_1146860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_1146860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146860 prefixEnd_1146860 := by exact prefixLift 1146860
  have htrace : WordTrace (prefixWord ++ tailWord_1146860) baseStart_1146860 baseEnd_1146860 := by
    simpa [prefixWord, tailWord_1146860, baseEnd_1146860] using wordTrace_append hprefix tailTrace_1146860
  have hstable : (prefixWord ++ tailWord_1146860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146860).length < 2 ^ (prefixWord ++ tailWord_1146860).sum := by decide
  have hdescent : baseEnd_1146860 < baseStart_1146860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146862 : List Nat := [4, 1, 2, 1, 3, 1, 2, 8]
def baseStart_1146862 : Nat := 118140960795 + 1146862 * 2 ^ 59
def prefixEnd_1146862 : Nat := 4983230072969 + 3 ^ 40 * 1146862 * 2
def baseEnd_1146862 : Nat := 43621588916799787470421

theorem tailTrace_1146862 : CollatzResearch.WordTrace tailWord_1146862 prefixEnd_1146862 43621588916799787470421 := by
  unfold tailWord_1146862
  simp only [CollatzResearch.WordTrace]
  refine ⟨5228686696390289660103355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27886329047414878187217893 5228686696390289660103355)
  ·
    refine ⟨7843030044585434490155033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5228686696390289660103355 7843030044585434490155033)
    ·
      refine ⟨5882272533439075867616275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7843030044585434490155033 5882272533439075867616275)
      ·
        refine ⟨8823408800158613801424413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5882272533439075867616275 8823408800158613801424413)
        ·
          refine ⟨3308778300059480175534155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8823408800158613801424413 3308778300059480175534155)
          ·
            refine ⟨4963167450089220263301233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3308778300059480175534155 4963167450089220263301233)
            ·
              refine ⟨3722375587566915197475925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4963167450089220263301233 3722375587566915197475925)
              ·
                refine ⟨43621588916799787470421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3722375587566915197475925 43621588916799787470421)
                ·
                  rfl

theorem cell22_1146862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_1146862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146862 prefixEnd_1146862 := by exact prefixLift 1146862
  have htrace : WordTrace (prefixWord ++ tailWord_1146862) baseStart_1146862 baseEnd_1146862 := by
    simpa [prefixWord, tailWord_1146862, baseEnd_1146862] using wordTrace_append hprefix tailTrace_1146862
  have hstable : (prefixWord ++ tailWord_1146862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146862).length < 2 ^ (prefixWord ++ tailWord_1146862).sum := by decide
  have hdescent : baseEnd_1146862 < baseStart_1146862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146894 : List Nat := [4, 1, 1, 2, 2, 1, 2, 3, 3, 3]
def baseStart_1146894 : Nat := 118140960795 + 1146894 * 2 ^ 59
def prefixEnd_1146894 : Nat := 4983230072969 + 3 ^ 40 * 1146894 * 2
def baseEnd_1146894 : Nat := 392605254505160670433691

theorem tailTrace_1146894 : CollatzResearch.WordTrace tailWord_1146894 prefixEnd_1146894 392605254505160670433691 := by
  unfold tailWord_1146894
  simp only [CollatzResearch.WordTrace]
  refine ⟨5228832588375798343248967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27887107138004257830661157 5228832588375798343248967)
  ·
    refine ⟨7843248882563697514873451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5228832588375798343248967 7843248882563697514873451)
    ·
      refine ⟨11764873323845546272310177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7843248882563697514873451 11764873323845546272310177)
      ·
        refine ⟨8823654992884159704232633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11764873323845546272310177 8823654992884159704232633)
        ·
          refine ⟨6617741244663119778174475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8823654992884159704232633 6617741244663119778174475)
          ·
            refine ⟨9926611866994679667261713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6617741244663119778174475 9926611866994679667261713)
            ·
              refine ⟨7444958900246009750446285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9926611866994679667261713 7444958900246009750446285)
              ·
                refine ⟨2791859587592253656417357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7444958900246009750446285 2791859587592253656417357)
                ·
                  refine ⟨1046947345347095121156509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2791859587592253656417357 1046947345347095121156509)
                  ·
                    refine ⟨392605254505160670433691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1046947345347095121156509 392605254505160670433691)
                    ·
                      rfl

theorem cell22_1146894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_1146894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146894 prefixEnd_1146894 := by exact prefixLift 1146894
  have htrace : WordTrace (prefixWord ++ tailWord_1146894) baseStart_1146894 baseEnd_1146894 := by
    simpa [prefixWord, tailWord_1146894, baseEnd_1146894] using wordTrace_append hprefix tailTrace_1146894
  have hstable : (prefixWord ++ tailWord_1146894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146894).length < 2 ^ (prefixWord ++ tailWord_1146894).sum := by decide
  have hdescent : baseEnd_1146894 < baseStart_1146894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146999 : List Nat := [1, 1, 3, 1, 1, 6, 1, 2, 2, 4]
def baseStart_1146999 : Nat := 118140960795 + 1146999 * 2 ^ 59
def prefixEnd_1146999 : Nat := 4983230072969 + 3 ^ 40 * 1146999 * 2
def baseEnd_1146999 : Nat := 392641198150975396558369

theorem tailTrace_1146999 : CollatzResearch.WordTrace tailWord_1146999 prefixEnd_1146999 392641198150975396558369 := by
  unfold tailWord_1146999
  simp only [CollatzResearch.WordTrace]
  refine ⟨41834490371625989678564051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27889660247750659785709367 41834490371625989678564051)
  ·
    refine ⟨62751735557438984517846077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41834490371625989678564051 62751735557438984517846077)
    ·
      refine ⟨23531900834039619194192279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62751735557438984517846077 23531900834039619194192279)
      ·
        refine ⟨35297851251059428791288419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23531900834039619194192279 35297851251059428791288419)
        ·
          refine ⟨52946776876589143186932629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35297851251059428791288419 52946776876589143186932629)
          ·
            refine ⟨2481880166090116086887467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 52946776876589143186932629 2481880166090116086887467)
            ·
              refine ⟨3722820249135174130331201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2481880166090116086887467 3722820249135174130331201)
              ·
                refine ⟨2792115186851380597748401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3722820249135174130331201 2792115186851380597748401)
                ·
                  refine ⟨2094086390138535448311301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2792115186851380597748401 2094086390138535448311301)
                  ·
                    refine ⟨392641198150975396558369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2094086390138535448311301 392641198150975396558369)
                    ·
                      rfl

theorem cell22_1146999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_1146999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1146999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1146999 prefixEnd_1146999 := by exact prefixLift 1146999
  have htrace : WordTrace (prefixWord ++ tailWord_1146999) baseStart_1146999 baseEnd_1146999 := by
    simpa [prefixWord, tailWord_1146999, baseEnd_1146999] using wordTrace_append hprefix tailTrace_1146999
  have hstable : (prefixWord ++ tailWord_1146999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146999).length < 2 ^ (prefixWord ++ tailWord_1146999).sum := by decide
  have hdescent : baseEnd_1146999 < baseStart_1146999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147018 : List Nat := [3, 1, 2, 3, 1, 2, 4, 1, 2, 3]
def baseStart_1147018 : Nat := 118140960795 + 1147018 * 2 ^ 59
def prefixEnd_1147018 : Nat := 4983230072969 + 3 ^ 40 * 1147018 * 2
def baseEnd_1147018 : Nat := 392647702239265680333311

theorem tailTrace_1147018 : CollatzResearch.WordTrace tailWord_1147018 prefixEnd_1147018 392647702239265680333311 := by
  unfold tailWord_1147018
  simp only [CollatzResearch.WordTrace]
  refine ⟨10458795839639288980876427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27890122239038103949003805 10458795839639288980876427)
  ·
    refine ⟨15688193759458933471314641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10458795839639288980876427 15688193759458933471314641)
    ·
      refine ⟨11766145319594200103485981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15688193759458933471314641 11766145319594200103485981)
      ·
        refine ⟨4412304494847825038807243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11766145319594200103485981 4412304494847825038807243)
        ·
          refine ⟨6618456742271737558210865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4412304494847825038807243 6618456742271737558210865)
          ·
            refine ⟨4963842556703803168658149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6618456742271737558210865 4963842556703803168658149)
            ·
              refine ⟨930720479381963094123403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4963842556703803168658149 930720479381963094123403)
              ·
                refine ⟨1396080719072944641185105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 930720479381963094123403 1396080719072944641185105)
                ·
                  refine ⟨1047060539304708480888829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1396080719072944641185105 1047060539304708480888829)
                  ·
                    refine ⟨392647702239265680333311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1047060539304708480888829 392647702239265680333311)
                    ·
                      rfl

theorem cell22_1147018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_1147018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147018 prefixEnd_1147018 := by exact prefixLift 1147018
  have htrace : WordTrace (prefixWord ++ tailWord_1147018) baseStart_1147018 baseEnd_1147018 := by
    simpa [prefixWord, tailWord_1147018, baseEnd_1147018] using wordTrace_append hprefix tailTrace_1147018
  have hstable : (prefixWord ++ tailWord_1147018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147018).length < 2 ^ (prefixWord ++ tailWord_1147018).sum := by decide
  have hdescent : baseEnd_1147018 < baseStart_1147018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147029 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 5, 3]
def baseStart_1147029 : Nat := 118140960795 + 1147029 * 2 ^ 59
def prefixEnd_1147029 : Nat := 4983230072969 + 3 ^ 40 * 1147029 * 2
def baseEnd_1147029 : Nat := 392651467764065318308277

theorem tailTrace_1147029 : CollatzResearch.WordTrace tailWord_1147029 prefixEnd_1147029 392651467764065318308277 := by
  unfold tailWord_1147029
  simp only [CollatzResearch.WordTrace]
  refine ⟨41835584561517304802156141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27890389707678203201437427 41835584561517304802156141)
  ·
    refine ⟨15688344210568989300808553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41835584561517304802156141 15688344210568989300808553)
    ·
      refine ⟨11766258157926741975606415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15688344210568989300808553 11766258157926741975606415)
      ·
        refine ⟨17649387236890112963409623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11766258157926741975606415 17649387236890112963409623)
        ·
          refine ⟨26474080855335169445114435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17649387236890112963409623 26474080855335169445114435)
          ·
            refine ⟨39711121283002754167671653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26474080855335169445114435 39711121283002754167671653)
            ·
              refine ⟨7445835240563016406438435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39711121283002754167671653 7445835240563016406438435)
              ·
                refine ⟨11168752860844524609657653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7445835240563016406438435 11168752860844524609657653)
                ·
                  refine ⟨1047070580704174182155405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11168752860844524609657653 1047070580704174182155405)
                  ·
                    refine ⟨392651467764065318308277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1047070580704174182155405 392651467764065318308277)
                    ·
                      rfl

theorem cell22_1147029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_1147029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147029 prefixEnd_1147029 := by exact prefixLift 1147029
  have htrace : WordTrace (prefixWord ++ tailWord_1147029) baseStart_1147029 baseEnd_1147029 := by
    simpa [prefixWord, tailWord_1147029, baseEnd_1147029] using wordTrace_append hprefix tailTrace_1147029
  have hstable : (prefixWord ++ tailWord_1147029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147029).length < 2 ^ (prefixWord ++ tailWord_1147029).sum := by decide
  have hdescent : baseEnd_1147029 < baseStart_1147029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147054 : List Nat := [4, 1, 4, 2, 2, 1, 2, 2, 4]
def baseStart_1147054 : Nat := 118140960795 + 1147054 * 2 ^ 59
def prefixEnd_1147054 : Nat := 4983230072969 + 3 ^ 40 * 1147054 * 2
def baseEnd_1147054 : Nat := 130886675258324528811067

theorem tailTrace_1147054 : CollatzResearch.WordTrace tailWord_1147054 prefixEnd_1147054 130886675258324528811067 := by
  unfold tailWord_1147054
  simp only [CollatzResearch.WordTrace]
  refine ⟨5229562048303341758977027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27890997590951156047877477 5229562048303341758977027)
  ·
    refine ⟨7844343072455012638465541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5229562048303341758977027 7844343072455012638465541)
    ·
      refine ⟨1470814326085314869712289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7844343072455012638465541 1470814326085314869712289)
      ·
        refine ⟨1103110744563986152284217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1470814326085314869712289 1103110744563986152284217)
        ·
          refine ⟨827333058422989614213163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1103110744563986152284217 827333058422989614213163)
          ·
            refine ⟨1240999587634484421319745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827333058422989614213163 1240999587634484421319745)
            ·
              refine ⟨930749690725863315989809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1240999587634484421319745 930749690725863315989809)
              ·
                refine ⟨698062268044397486992357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 930749690725863315989809 698062268044397486992357)
                ·
                  refine ⟨130886675258324528811067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 698062268044397486992357 130886675258324528811067)
                  ·
                    rfl

theorem cell22_1147054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_1147054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147054 prefixEnd_1147054 := by exact prefixLift 1147054
  have htrace : WordTrace (prefixWord ++ tailWord_1147054) baseStart_1147054 baseEnd_1147054 := by
    simpa [prefixWord, tailWord_1147054, baseEnd_1147054] using wordTrace_append hprefix tailTrace_1147054
  have hstable : (prefixWord ++ tailWord_1147054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147054).length < 2 ^ (prefixWord ++ tailWord_1147054).sum := by decide
  have hdescent : baseEnd_1147054 < baseStart_1147054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147063 : List Nat := [1, 1, 3, 1, 4, 3, 1, 4, 1, 3]
def baseStart_1147063 : Nat := 118140960795 + 1147063 * 2 ^ 59
def prefixEnd_1147063 : Nat := 4983230072969 + 3 ^ 40 * 1147063 * 2
def baseEnd_1147063 : Nat := 392663106658900562958173

theorem tailTrace_1147063 : CollatzResearch.WordTrace tailWord_1147063 prefixEnd_1147063 392663106658900562958173 := by
  unfold tailWord_1147063
  simp only [CollatzResearch.WordTrace]
  refine ⟨41836824643394128608893843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27891216428929419072595895 41836824643394128608893843)
  ·
    refine ⟨62755236965091192913340765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41836824643394128608893843 62755236965091192913340765)
    ·
      refine ⟨23533213861909197342502787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62755236965091192913340765 23533213861909197342502787)
      ·
        refine ⟨35299820792863796013754181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23533213861909197342502787 35299820792863796013754181)
        ·
          refine ⟨6618716398661961752578909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35299820792863796013754181 6618716398661961752578909)
          ·
            refine ⟨2482018649498235657217091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6618716398661961752578909 2482018649498235657217091)
            ·
              refine ⟨3723027974247353485825637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2482018649498235657217091 3723027974247353485825637)
              ·
                refine ⟨698067745171378778592307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3723027974247353485825637 698067745171378778592307)
                ·
                  refine ⟨1047101617757068167888461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 698067745171378778592307 1047101617757068167888461)
                  ·
                    refine ⟨392663106658900562958173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1047101617757068167888461 392663106658900562958173)
                    ·
                      rfl

theorem cell22_1147063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 1, 3].length) (baseStart_1147063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147063 prefixEnd_1147063 := by exact prefixLift 1147063
  have htrace : WordTrace (prefixWord ++ tailWord_1147063) baseStart_1147063 baseEnd_1147063 := by
    simpa [prefixWord, tailWord_1147063, baseEnd_1147063] using wordTrace_append hprefix tailTrace_1147063
  have hstable : (prefixWord ++ tailWord_1147063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147063).length < 2 ^ (prefixWord ++ tailWord_1147063).sum := by decide
  have hdescent : baseEnd_1147063 < baseStart_1147063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147076 : List Nat := [2, 3, 3, 1, 2, 1, 2, 3, 5]
def baseStart_1147076 : Nat := 118140960795 + 1147076 * 2 ^ 59
def prefixEnd_1147076 : Nat := 4983230072969 + 3 ^ 40 * 1147076 * 2
def baseEnd_1147076 : Nat := 130889185608190954127711

theorem tailTrace_1147076 : CollatzResearch.WordTrace tailWord_1147076 prefixEnd_1147076 130889185608190954127711 := by
  unfold tailWord_1147076
  simp only [CollatzResearch.WordTrace]
  refine ⟨20918649396173515914558541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27891532528231354552744721 20918649396173515914558541)
  ·
    refine ⟨7844493523565068467959453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20918649396173515914558541 7844493523565068467959453)
    ·
      refine ⟨2941685071336900675484795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7844493523565068467959453 2941685071336900675484795)
      ·
        refine ⟨4412527607005351013227193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2941685071336900675484795 4412527607005351013227193)
        ·
          refine ⟨3309395705254013259920395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4412527607005351013227193 3309395705254013259920395)
          ·
            refine ⟨4964093557881019889880593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3309395705254013259920395 4964093557881019889880593)
            ·
              refine ⟨3723070168410764917410445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4964093557881019889880593 3723070168410764917410445)
              ·
                refine ⟨1396151313154036844028917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3723070168410764917410445 1396151313154036844028917)
                ·
                  refine ⟨130889185608190954127711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1396151313154036844028917 130889185608190954127711)
                  ·
                    rfl

theorem cell22_1147076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_1147076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147076 prefixEnd_1147076 := by exact prefixLift 1147076
  have htrace : WordTrace (prefixWord ++ tailWord_1147076) baseStart_1147076 baseEnd_1147076 := by
    simpa [prefixWord, tailWord_1147076, baseEnd_1147076] using wordTrace_append hprefix tailTrace_1147076
  have hstable : (prefixWord ++ tailWord_1147076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147076).length < 2 ^ (prefixWord ++ tailWord_1147076).sum := by decide
  have hdescent : baseEnd_1147076 < baseStart_1147076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147089 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 3, 4]
def baseStart_1147089 : Nat := 118140960795 + 1147089 * 2 ^ 59
def prefixEnd_1147089 : Nat := 4983230072969 + 3 ^ 40 * 1147089 * 2
def baseEnd_1147089 : Nat := 392672006990245161808093

theorem tailTrace_1147089 : CollatzResearch.WordTrace tailWord_1147089 prefixEnd_1147089 392672006990245161808093 := by
  unfold tailWord_1147089
  simp only [CollatzResearch.WordTrace]
  refine ⟨41837772941299935049340321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27891848627533290032893547 41837772941299935049340321)
  ·
    refine ⟨31378329705974951287005241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41837772941299935049340321 31378329705974951287005241)
    ·
      refine ⟨23533747279481213465253931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31378329705974951287005241 23533747279481213465253931)
      ·
        refine ⟨35300620919221820197880897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23533747279481213465253931 35300620919221820197880897)
        ·
          refine ⟨26475465689416365148410673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35300620919221820197880897 26475465689416365148410673)
          ·
            refine ⟨19856599267062273861308005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26475465689416365148410673 19856599267062273861308005)
            ·
              refine ⟨3723112362574176348995251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19856599267062273861308005 3723112362574176348995251)
              ·
                refine ⟨5584668543861264523492877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3723112362574176348995251 5584668543861264523492877)
                ·
                  refine ⟨2094250703947974196309829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5584668543861264523492877 2094250703947974196309829)
                  ·
                    refine ⟨392672006990245161808093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2094250703947974196309829 392672006990245161808093)
                    ·
                      rfl

theorem cell22_1147089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_1147089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147089 prefixEnd_1147089 := by exact prefixLift 1147089
  have htrace : WordTrace (prefixWord ++ tailWord_1147089) baseStart_1147089 baseEnd_1147089 := by
    simpa [prefixWord, tailWord_1147089, baseEnd_1147089] using wordTrace_append hprefix tailTrace_1147089
  have hstable : (prefixWord ++ tailWord_1147089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147089).length < 2 ^ (prefixWord ++ tailWord_1147089).sum := by decide
  have hdescent : baseEnd_1147089 < baseStart_1147089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147121 : List Nat := [1, 2, 2, 2, 2, 1, 4, 4, 4]
def baseStart_1147121 : Nat := 118140960795 + 1147121 * 2 ^ 59
def prefixEnd_1147121 : Nat := 4983230072969 + 3 ^ 40 * 1147121 * 2
def baseEnd_1147121 : Nat := 130894320414735915002665

theorem tailTrace_1147121 : CollatzResearch.WordTrace tailWord_1147121 prefixEnd_1147121 130894320414735915002665 := by
  unfold tailWord_1147121
  simp only [CollatzResearch.WordTrace]
  refine ⟨41838940077184004514505217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27892626718122669676336811 41838940077184004514505217)
  ·
    refine ⟨31379205057888003385878913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41838940077184004514505217 31379205057888003385878913)
    ·
      refine ⟨23534403793416002539409185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31379205057888003385878913 23534403793416002539409185)
      ·
        refine ⟨17650802845062001904556889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23534403793416002539409185 17650802845062001904556889)
        ·
          refine ⟨13238102133796501428417667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17650802845062001904556889 13238102133796501428417667)
          ·
            refine ⟨19857153200694752142626501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13238102133796501428417667 19857153200694752142626501)
            ·
              refine ⟨3723216225130266026742469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19857153200694752142626501 3723216225130266026742469)
              ·
                refine ⟨698103042211924880014213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3723216225130266026742469 698103042211924880014213)
                ·
                  refine ⟨130894320414735915002665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 698103042211924880014213 130894320414735915002665)
                  ·
                    rfl

theorem cell22_1147121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 4].length) (baseStart_1147121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147121 prefixEnd_1147121 := by exact prefixLift 1147121
  have htrace : WordTrace (prefixWord ++ tailWord_1147121) baseStart_1147121 baseEnd_1147121 := by
    simpa [prefixWord, tailWord_1147121, baseEnd_1147121] using wordTrace_append hprefix tailTrace_1147121
  have hstable : (prefixWord ++ tailWord_1147121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147121).length < 2 ^ (prefixWord ++ tailWord_1147121).sum := by decide
  have hdescent : baseEnd_1147121 < baseStart_1147121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147136 : List Nat := [2, 1, 1, 2, 1, 1, 4, 5, 2, 3]
def baseStart_1147136 : Nat := 118140960795 + 1147136 * 2 ^ 59
def prefixEnd_1147136 : Nat := 4983230072969 + 3 ^ 40 * 1147136 * 2
def baseEnd_1147136 : Nat := 392688096050752705882949

theorem tailTrace_1147136 : CollatzResearch.WordTrace tailWord_1147136 prefixEnd_1147136 392688096050752705882949 := by
  unfold tailWord_1147136
  simp only [CollatzResearch.WordTrace]
  refine ⟨20919743586064831038150631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27892991448086441384200841 20919743586064831038150631)
  ·
    refine ⟨31379615379097246557225947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20919743586064831038150631 31379615379097246557225947)
    ·
      refine ⟨47069423068645869835838921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31379615379097246557225947 47069423068645869835838921)
      ·
        refine ⟨35302067301484402376879191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47069423068645869835838921 35302067301484402376879191)
        ·
          refine ⟨52953100952226603565318787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35302067301484402376879191 52953100952226603565318787)
          ·
            refine ⟨79429651428339905347978181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52953100952226603565318787 79429651428339905347978181)
            ·
              refine ⟨14893059642813732252745909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79429651428339905347978181 14893059642813732252745909)
              ·
                refine ⟨1396224341513787398694929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14893059642813732252745909 1396224341513787398694929)
                ·
                  refine ⟨1047168256135340549021197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1396224341513787398694929 1047168256135340549021197)
                  ·
                    refine ⟨392688096050752705882949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1047168256135340549021197 392688096050752705882949)
                    ·
                      rfl

theorem cell22_1147136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 2, 3].length) (baseStart_1147136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147136 prefixEnd_1147136 := by exact prefixLift 1147136
  have htrace : WordTrace (prefixWord ++ tailWord_1147136) baseStart_1147136 baseEnd_1147136 := by
    simpa [prefixWord, tailWord_1147136, baseEnd_1147136] using wordTrace_append hprefix tailTrace_1147136
  have hstable : (prefixWord ++ tailWord_1147136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147136).length < 2 ^ (prefixWord ++ tailWord_1147136).sum := by decide
  have hdescent : baseEnd_1147136 < baseStart_1147136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147209 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 4, 5]
def baseStart_1147209 : Nat := 118140960795 + 1147209 * 2 ^ 59
def prefixEnd_1147209 : Nat := 4983230072969 + 3 ^ 40 * 1147209 * 2
def baseEnd_1147209 : Nat := 392713085442604848807725

theorem tailTrace_1147209 : CollatzResearch.WordTrace tailWord_1147209 prefixEnd_1147209 392713085442604848807725 := by
  unfold tailWord_1147209
  simp only [CollatzResearch.WordTrace]
  refine ⟨41842149700865195543708681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27894766467243463695805787 41842149700865195543708681)
  ·
    refine ⟨31381612275648896657781511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41842149700865195543708681 31381612275648896657781511)
    ·
      refine ⟨47072418413473344986672267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31381612275648896657781511 47072418413473344986672267)
      ·
        refine ⟨70608627620210017480008401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47072418413473344986672267 70608627620210017480008401)
        ·
          refine ⟨52956470715157513110006301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70608627620210017480008401 52956470715157513110006301)
          ·
            refine ⟨19858676518184067416252363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52956470715157513110006301 19858676518184067416252363)
            ·
              refine ⟨29788014777276101124378545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19858676518184067416252363 29788014777276101124378545)
              ·
                refine ⟨22341011082957075843283909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29788014777276101124378545 22341011082957075843283909)
                ·
                  refine ⟨4188939578054451720615733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22341011082957075843283909 4188939578054451720615733)
                  ·
                    refine ⟨392713085442604848807725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4188939578054451720615733 392713085442604848807725)
                    ·
                      rfl

theorem cell22_1147209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_1147209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147209 prefixEnd_1147209 := by exact prefixLift 1147209
  have htrace : WordTrace (prefixWord ++ tailWord_1147209) baseStart_1147209 baseEnd_1147209 := by
    simpa [prefixWord, tailWord_1147209, baseEnd_1147209] using wordTrace_append hprefix tailTrace_1147209
  have hstable : (prefixWord ++ tailWord_1147209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147209).length < 2 ^ (prefixWord ++ tailWord_1147209).sum := by decide
  have hdescent : baseEnd_1147209 < baseStart_1147209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147271 : List Nat := [1, 1, 4, 2, 2, 1, 1, 4, 1, 5]
def baseStart_1147271 : Nat := 118140960795 + 1147271 * 2 ^ 59
def prefixEnd_1147271 : Nat := 4983230072969 + 3 ^ 40 * 1147271 * 2
def baseEnd_1147271 : Nat := 392734309309657353757535

theorem tailTrace_1147271 : CollatzResearch.WordTrace tailWord_1147271 prefixEnd_1147271 392734309309657353757535 := by
  unfold tailWord_1147271
  simp only [CollatzResearch.WordTrace]
  refine ⟨41844411026640580132465667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27896274017760386754977111 41844411026640580132465667)
  ·
    refine ⟨62766616539960870198698501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41844411026640580132465667 62766616539960870198698501)
    ·
      refine ⟨11768740601242663162255969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62766616539960870198698501 11768740601242663162255969)
      ·
        refine ⟨8826555450931997371691977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11768740601242663162255969 8826555450931997371691977)
        ·
          refine ⟨6619916588198998028768983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8826555450931997371691977 6619916588198998028768983)
          ·
            refine ⟨9929874882298497043153475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6619916588198998028768983 9929874882298497043153475)
            ·
              refine ⟨14894812323447745564730213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9929874882298497043153475 14894812323447745564730213)
              ·
                refine ⟨2792777310646452293386915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14894812323447745564730213 2792777310646452293386915)
                ·
                  refine ⟨4189165965969678440080373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2792777310646452293386915 4189165965969678440080373)
                  ·
                    refine ⟨392734309309657353757535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4189165965969678440080373 392734309309657353757535)
                    ·
                      rfl

theorem cell22_1147271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_1147271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147271 prefixEnd_1147271 := by exact prefixLift 1147271
  have htrace : WordTrace (prefixWord ++ tailWord_1147271) baseStart_1147271 baseEnd_1147271 := by
    simpa [prefixWord, tailWord_1147271, baseEnd_1147271] using wordTrace_append hprefix tailTrace_1147271
  have hstable : (prefixWord ++ tailWord_1147271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147271).length < 2 ^ (prefixWord ++ tailWord_1147271).sum := by decide
  have hdescent : baseEnd_1147271 < baseStart_1147271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147273 : List Nat := [1, 2, 1, 1, 6, 1, 1, 5, 4]
def baseStart_1147273 : Nat := 118140960795 + 1147273 * 2 ^ 59
def prefixEnd_1147273 : Nat := 4983230072969 + 3 ^ 40 * 1147273 * 2
def baseEnd_1147273 : Nat := 130911664650176671735843

theorem tailTrace_1147273 : CollatzResearch.WordTrace tailWord_1147273 prefixEnd_1147273 130911664650176671735843 := by
  unfold tailWord_1147273
  simp only [CollatzResearch.WordTrace]
  refine ⟨41844483972633334474038473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27896322648422222982692315 41844483972633334474038473)
  ·
    refine ⟨31383362979475000855528855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41844483972633334474038473 31383362979475000855528855)
    ·
      refine ⟨47075044469212501283293283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31383362979475000855528855 47075044469212501283293283)
      ·
        refine ⟨70612566703818751924939925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47075044469212501283293283 70612566703818751924939925)
        ·
          refine ⟨3309964064241503996481559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 70612566703818751924939925 3309964064241503996481559)
          ·
            refine ⟨4964946096362255994722339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3309964064241503996481559 4964946096362255994722339)
            ·
              refine ⟨7447419144543383992083509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4964946096362255994722339 7447419144543383992083509)
              ·
                refine ⟨698195544800942249257829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7447419144543383992083509 698195544800942249257829)
                ·
                  refine ⟨130911664650176671735843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 698195544800942249257829 130911664650176671735843)
                  ·
                    rfl

theorem cell22_1147273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 4].length) (baseStart_1147273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147273 prefixEnd_1147273 := by exact prefixLift 1147273
  have htrace : WordTrace (prefixWord ++ tailWord_1147273) baseStart_1147273 baseEnd_1147273 := by
    simpa [prefixWord, tailWord_1147273, baseEnd_1147273] using wordTrace_append hprefix tailTrace_1147273
  have hstable : (prefixWord ++ tailWord_1147273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147273).length < 2 ^ (prefixWord ++ tailWord_1147273).sum := by decide
  have hdescent : baseEnd_1147273 < baseStart_1147273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147275 : List Nat := [1, 1, 1, 1, 4, 6, 2, 1, 1, 4]
def baseStart_1147275 : Nat := 118140960795 + 1147275 * 2 ^ 59
def prefixEnd_1147275 : Nat := 4983230072969 + 3 ^ 40 * 1147275 * 2
def baseEnd_1147275 : Nat := 392735678591402676657523

theorem tailTrace_1147275 : CollatzResearch.WordTrace tailWord_1147275 prefixEnd_1147275 392735678591402676657523 := by
  unfold tailWord_1147275
  simp only [CollatzResearch.WordTrace]
  refine ⟨41844556918626088815611279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27896371279084059210407519 41844556918626088815611279)
  ·
    refine ⟨62766835377939133223416919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41844556918626088815611279 62766835377939133223416919)
    ·
      refine ⟨94150253066908699835125379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62766835377939133223416919 94150253066908699835125379)
      ·
        refine ⟨141225379600363049752688069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94150253066908699835125379 141225379600363049752688069)
        ·
          refine ⟨26479758675068071828629013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141225379600363049752688069 26479758675068071828629013)
          ·
            refine ⟨1241238687893815866966985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26479758675068071828629013 1241238687893815866966985)
            ·
              refine ⟨930929015920361900225239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1241238687893815866966985 930929015920361900225239)
              ·
                refine ⟨1396393523880542850337859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 930929015920361900225239 1396393523880542850337859)
                ·
                  refine ⟨2094590285820814275506789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1396393523880542850337859 2094590285820814275506789)
                  ·
                    refine ⟨392735678591402676657523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2094590285820814275506789 392735678591402676657523)
                    ·
                      rfl

theorem cell22_1147275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 1, 4].length) (baseStart_1147275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147275 prefixEnd_1147275 := by exact prefixLift 1147275
  have htrace : WordTrace (prefixWord ++ tailWord_1147275) baseStart_1147275 baseEnd_1147275 := by
    simpa [prefixWord, tailWord_1147275, baseEnd_1147275] using wordTrace_append hprefix tailTrace_1147275
  have hstable : (prefixWord ++ tailWord_1147275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147275).length < 2 ^ (prefixWord ++ tailWord_1147275).sum := by decide
  have hdescent : baseEnd_1147275 < baseStart_1147275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147361 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 1, 7]
def baseStart_1147361 : Nat := 118140960795 + 1147361 * 2 ^ 59
def prefixEnd_1147361 : Nat := 4983230072969 + 3 ^ 40 * 1147361 * 2
def baseEnd_1147361 : Nat := 392765118148927119007259

theorem tailTrace_1147361 : CollatzResearch.WordTrace tailWord_1147361 prefixEnd_1147361 392765118148927119007259 := by
  unfold tailWord_1147361
  simp only [CollatzResearch.WordTrace]
  refine ⟨41847693596314525503241937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27898462397543017002161291 41847693596314525503241937)
  ·
    refine ⟨31385770197235894127431453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41847693596314525503241937 31385770197235894127431453)
    ·
      refine ⟨11769663823963460297786795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31385770197235894127431453 11769663823963460297786795)
      ·
        refine ⟨17654495735945190446680193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11769663823963460297786795 17654495735945190446680193)
        ·
          refine ⟨13240871801958892835010145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17654495735945190446680193 13240871801958892835010145)
          ·
            refine ⟨9930653851469169626257609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13240871801958892835010145 9930653851469169626257609)
            ·
              refine ⟨7447990388601877219693207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9930653851469169626257609 7447990388601877219693207)
              ·
                refine ⟨11171985582902815829539811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7447990388601877219693207 11171985582902815829539811)
                ·
                  refine ⟨16757978374354223744309717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11171985582902815829539811 16757978374354223744309717)
                  ·
                    refine ⟨392765118148927119007259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16757978374354223744309717 392765118148927119007259)
                    ·
                      rfl

theorem cell22_1147361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_1147361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147361 prefixEnd_1147361 := by exact prefixLift 1147361
  have htrace : WordTrace (prefixWord ++ tailWord_1147361) baseStart_1147361 baseEnd_1147361 := by
    simpa [prefixWord, tailWord_1147361, baseEnd_1147361] using wordTrace_append hprefix tailTrace_1147361
  have hstable : (prefixWord ++ tailWord_1147361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147361).length < 2 ^ (prefixWord ++ tailWord_1147361).sum := by decide
  have hdescent : baseEnd_1147361 < baseStart_1147361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147423 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 6, 3]
def baseStart_1147423 : Nat := 118140960795 + 1147423 * 2 ^ 59
def prefixEnd_1147423 : Nat := 4983230072969 + 3 ^ 40 * 1147423 * 2
def baseEnd_1147423 : Nat := 392786342015979623957069

theorem tailTrace_1147423 : CollatzResearch.WordTrace tailWord_1147423 prefixEnd_1147423 392786342015979623957069 := by
  unfold tailWord_1147423
  simp only [CollatzResearch.WordTrace]
  refine ⟨41849954922089910091998923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27899969948059940061332615 41849954922089910091998923)
  ·
    refine ⟨62774932383134865137998385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41849954922089910091998923 62774932383134865137998385)
    ·
      refine ⟨47081199287351148853498789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62774932383134865137998385 47081199287351148853498789)
      ·
        refine ⟨8827724866378340410031023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47081199287351148853498789 8827724866378340410031023)
        ·
          refine ⟨13241587299567510615046535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8827724866378340410031023 13241587299567510615046535)
          ·
            refine ⟨19862380949351265922569803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13241587299567510615046535 19862380949351265922569803)
            ·
              refine ⟨29793571424026898883854705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19862380949351265922569803 29793571424026898883854705)
              ·
                refine ⟨22345178568020174162891029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29793571424026898883854705 22345178568020174162891029)
                ·
                  refine ⟨1047430245375945663885517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22345178568020174162891029 1047430245375945663885517)
                  ·
                    refine ⟨392786342015979623957069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1047430245375945663885517 392786342015979623957069)
                    ·
                      rfl

theorem cell22_1147423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 3].length) (baseStart_1147423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147423 prefixEnd_1147423 := by exact prefixLift 1147423
  have htrace : WordTrace (prefixWord ++ tailWord_1147423) baseStart_1147423 baseEnd_1147423 := by
    simpa [prefixWord, tailWord_1147423, baseEnd_1147423] using wordTrace_append hprefix tailTrace_1147423
  have hstable : (prefixWord ++ tailWord_1147423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147423).length < 2 ^ (prefixWord ++ tailWord_1147423).sum := by decide
  have hdescent : baseEnd_1147423 < baseStart_1147423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147436 : List Nat := [2, 2, 1, 1, 1, 2, 1, 12]
def baseStart_1147436 : Nat := 118140960795 + 1147436 * 2 ^ 59
def prefixEnd_1147436 : Nat := 4983230072969 + 3 ^ 40 * 1147436 * 2
def baseEnd_1147436 : Nat := 43643421353516880375781

theorem tailTrace_1147436 : CollatzResearch.WordTrace tailWord_1147436 prefixEnd_1147436 43643421353516880375781 := by
  unfold tailWord_1147436
  simp only [CollatzResearch.WordTrace]
  refine ⟨20925214535521406656111081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27900286047361875541481441 20925214535521406656111081)
  ·
    refine ⟨15693910901641054992083311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20925214535521406656111081 15693910901641054992083311)
    ·
      refine ⟨23540866352461582488124967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15693910901641054992083311 23540866352461582488124967)
      ·
        refine ⟨35311299528692373732187451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23540866352461582488124967 35311299528692373732187451)
        ·
          refine ⟨52966949293038560598281177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35311299528692373732187451 52966949293038560598281177)
          ·
            refine ⟨39725211969778920448710883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52966949293038560598281177 39725211969778920448710883)
            ·
              refine ⟨59587817954668380673066325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39725211969778920448710883 59587817954668380673066325)
              ·
                refine ⟨43643421353516880375781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 59587817954668380673066325 43643421353516880375781)
                ·
                  rfl

theorem cell22_1147436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 12].length) (baseStart_1147436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147436 prefixEnd_1147436 := by exact prefixLift 1147436
  have htrace : WordTrace (prefixWord ++ tailWord_1147436) baseStart_1147436 baseEnd_1147436 := by
    simpa [prefixWord, tailWord_1147436, baseEnd_1147436] using wordTrace_append hprefix tailTrace_1147436
  have hstable : (prefixWord ++ tailWord_1147436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147436).length < 2 ^ (prefixWord ++ tailWord_1147436).sum := by decide
  have hdescent : baseEnd_1147436 < baseStart_1147436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147444 : List Nat := [2, 5, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_1147444 : Nat := 118140960795 + 1147444 * 2 ^ 59
def prefixEnd_1147444 : Nat := 4983230072969 + 3 ^ 40 * 1147444 * 2
def baseEnd_1147444 : Nat := 392793530745142569182005

theorem tailTrace_1147444 : CollatzResearch.WordTrace tailWord_1147444 prefixEnd_1147444 392793530745142569182005 := by
  unfold tailWord_1147444
  simp only [CollatzResearch.WordTrace]
  refine ⟨20925360427506915339256693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27900480570009220452342257 20925360427506915339256693)
  ·
    refine ⟨1961752540078773313055315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20925360427506915339256693 1961752540078773313055315)
    ·
      refine ⟨2942628810118159969582973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1961752540078773313055315 2942628810118159969582973)
      ·
        refine ⟨1103485803794309988593615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2942628810118159969582973 1103485803794309988593615)
        ·
          refine ⟨1655228705691464982890423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1103485803794309988593615 1655228705691464982890423)
          ·
            refine ⟨2482843058537197474335635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1655228705691464982890423 2482843058537197474335635)
            ·
              refine ⟨3724264587805796211503453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2482843058537197474335635 3724264587805796211503453)
              ·
                refine ⟨1396599220427173579313795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3724264587805796211503453 1396599220427173579313795)
                ·
                  refine ⟨2094898830640760368970693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1396599220427173579313795 2094898830640760368970693)
                  ·
                    refine ⟨392793530745142569182005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2094898830640760368970693 392793530745142569182005)
                    ·
                      rfl

theorem cell22_1147444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_1147444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147444 prefixEnd_1147444 := by exact prefixLift 1147444
  have htrace : WordTrace (prefixWord ++ tailWord_1147444) baseStart_1147444 baseEnd_1147444 := by
    simpa [prefixWord, tailWord_1147444, baseEnd_1147444] using wordTrace_append hprefix tailTrace_1147444
  have hstable : (prefixWord ++ tailWord_1147444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147444).length < 2 ^ (prefixWord ++ tailWord_1147444).sum := by decide
  have hdescent : baseEnd_1147444 < baseStart_1147444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147453 : List Nat := [1, 4, 1, 3, 2, 2, 9]
def baseStart_1147453 : Nat := 118140960795 + 1147453 * 2 ^ 59
def prefixEnd_1147453 : Nat := 4983230072969 + 3 ^ 40 * 1147453 * 2
def baseEnd_1147453 : Nat := 14548022652928501692851

theorem tailTrace_1147453 : CollatzResearch.WordTrace tailWord_1147453 prefixEnd_1147453 14548022652928501692851 := by
  unfold tailWord_1147453
  simp only [CollatzResearch.WordTrace]
  refine ⟨41851049111981225215591013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27900699407987483477060675 41851049111981225215591013)
  ·
    refine ⟨7847071708496479727923315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41851049111981225215591013 7847071708496479727923315)
    ·
      refine ⟨11770607562744719591884973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7847071708496479727923315 11770607562744719591884973)
      ·
        refine ⟨4413977836029269846956865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11770607562744719591884973 4413977836029269846956865)
        ·
          refine ⟨3310483377021952385217649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4413977836029269846956865 3310483377021952385217649)
          ·
            refine ⟨2482862532766464288913237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3310483377021952385217649 2482862532766464288913237)
            ·
              refine ⟨14548022652928501692851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2482862532766464288913237 14548022652928501692851)
              ·
                rfl

theorem cell22_1147453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 9].length) (baseStart_1147453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147453 prefixEnd_1147453 := by exact prefixLift 1147453
  have htrace : WordTrace (prefixWord ++ tailWord_1147453) baseStart_1147453 baseEnd_1147453 := by
    simpa [prefixWord, tailWord_1147453, baseEnd_1147453] using wordTrace_append hprefix tailTrace_1147453
  have hstable : (prefixWord ++ tailWord_1147453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147453).length < 2 ^ (prefixWord ++ tailWord_1147453).sum := by decide
  have hdescent : baseEnd_1147453 < baseStart_1147453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147457 : List Nat := [1, 2, 5, 1, 1, 2, 3, 2, 2, 3]
def baseStart_1147457 : Nat := 118140960795 + 1147457 * 2 ^ 59
def prefixEnd_1147457 : Nat := 4983230072969 + 3 ^ 40 * 1147457 * 2
def baseEnd_1147457 : Nat := 392797980910814868606965

theorem tailTrace_1147457 : CollatzResearch.WordTrace tailWord_1147457 prefixEnd_1147457 392797980910814868606965 := by
  unfold tailWord_1147457
  simp only [CollatzResearch.WordTrace]
  refine ⟨41851195003966733898736625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27900796669311155932491083 41851195003966733898736625)
  ·
    refine ⟨31388396252975050424052469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41851195003966733898736625 31388396252975050424052469)
    ·
      refine ⟨2942662148716410977254919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31388396252975050424052469 2942662148716410977254919)
      ·
        refine ⟨4413993223074616465882379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2942662148716410977254919 4413993223074616465882379)
        ·
          refine ⟨6620989834611924698823569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4413993223074616465882379 6620989834611924698823569)
          ·
            refine ⟨4965742375958943524117677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6620989834611924698823569 4965742375958943524117677)
            ·
              refine ⟨1862153390984603821544129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4965742375958943524117677 1862153390984603821544129)
              ·
                refine ⟨1396615043238452866158097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1862153390984603821544129 1396615043238452866158097)
                ·
                  refine ⟨1047461282428839649618573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1396615043238452866158097 1047461282428839649618573)
                  ·
                    refine ⟨392797980910814868606965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1047461282428839649618573 392797980910814868606965)
                    ·
                      rfl

theorem cell22_1147457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_1147457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147457 prefixEnd_1147457 := by exact prefixLift 1147457
  have htrace : WordTrace (prefixWord ++ tailWord_1147457) baseStart_1147457 baseEnd_1147457 := by
    simpa [prefixWord, tailWord_1147457, baseEnd_1147457] using wordTrace_append hprefix tailTrace_1147457
  have hstable : (prefixWord ++ tailWord_1147457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147457).length < 2 ^ (prefixWord ++ tailWord_1147457).sum := by decide
  have hdescent : baseEnd_1147457 < baseStart_1147457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147498 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 9]
def baseStart_1147498 : Nat := 118140960795 + 1147498 * 2 ^ 59
def prefixEnd_1147498 : Nat := 4983230072969 + 3 ^ 40 * 1147498 * 2
def baseEnd_1147498 : Nat := 130937338682901476110613

theorem tailTrace_1147498 : CollatzResearch.WordTrace tailWord_1147498 prefixEnd_1147498 130937338682901476110613 := by
  unfold tailWord_1147498
  simp only [CollatzResearch.WordTrace]
  refine ⟨10463172599204549475244787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27901793597878798600652765 10463172599204549475244787)
  ·
    refine ⟨15694758898806824212867181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10463172599204549475244787 15694758898806824212867181)
    ·
      refine ⟨5885534587052559079825193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15694758898806824212867181 5885534587052559079825193)
      ·
        refine ⟨4414150940289419309868895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5885534587052559079825193 4414150940289419309868895)
        ·
          refine ⟨6621226410434128964803343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4414150940289419309868895 6621226410434128964803343)
          ·
            refine ⟨9931839615651193447205015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6621226410434128964803343 9931839615651193447205015)
            ·
              refine ⟨14897759423476790170807523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9931839615651193447205015 14897759423476790170807523)
              ·
                refine ⟨22346639135215185256211285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14897759423476790170807523 22346639135215185256211285)
                ·
                  refine ⟨130937338682901476110613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22346639135215185256211285 130937338682901476110613)
                  ·
                    rfl

theorem cell22_1147498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_1147498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147498 prefixEnd_1147498 := by exact prefixLift 1147498
  have htrace : WordTrace (prefixWord ++ tailWord_1147498) baseStart_1147498 baseEnd_1147498 := by
    simpa [prefixWord, tailWord_1147498, baseEnd_1147498] using wordTrace_append hprefix tailTrace_1147498
  have hstable : (prefixWord ++ tailWord_1147498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147498).length < 2 ^ (prefixWord ++ tailWord_1147498).sum := by decide
  have hdescent : baseEnd_1147498 < baseStart_1147498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147543 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 8]
def baseStart_1147543 : Nat := 118140960795 + 1147543 * 2 ^ 59
def prefixEnd_1147543 : Nat := 4983230072969 + 3 ^ 40 * 1147543 * 2
def baseEnd_1147543 : Nat := 130942473489446436985567

theorem tailTrace_1147543 : CollatzResearch.WordTrace tailWord_1147543 prefixEnd_1147543 130942473489446436985567 := by
  unfold tailWord_1147543
  simp only [CollatzResearch.WordTrace]
  refine ⟨41854331681655170586367283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27902887787770113724244855 41854331681655170586367283)
  ·
    refine ⟨62781497522482755879550925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41854331681655170586367283 62781497522482755879550925)
    ·
      refine ⟨23543061570931033454831597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62781497522482755879550925 23543061570931033454831597)
      ·
        refine ⟨8828648089099137545561849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23543061570931033454831597 8828648089099137545561849)
        ·
          refine ⟨6621486066824353159171387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8828648089099137545561849 6621486066824353159171387)
          ·
            refine ⟨9932229100236529738757081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6621486066824353159171387 9932229100236529738757081)
            ·
              refine ⟨7449171825177397304067811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9932229100236529738757081 7449171825177397304067811)
              ·
                refine ⟨11173757737766095956101717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7449171825177397304067811 11173757737766095956101717)
                ·
                  refine ⟨130942473489446436985567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11173757737766095956101717 130942473489446436985567)
                  ·
                    rfl

theorem cell22_1147543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 8].length) (baseStart_1147543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147543 prefixEnd_1147543 := by exact prefixLift 1147543
  have htrace : WordTrace (prefixWord ++ tailWord_1147543) baseStart_1147543 baseEnd_1147543 := by
    simpa [prefixWord, tailWord_1147543, baseEnd_1147543] using wordTrace_append hprefix tailTrace_1147543
  have hstable : (prefixWord ++ tailWord_1147543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147543).length < 2 ^ (prefixWord ++ tailWord_1147543).sum := by decide
  have hdescent : baseEnd_1147543 < baseStart_1147543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147592 : List Nat := [2, 1, 3, 1, 2, 3, 2, 3, 2, 3]
def baseStart_1147592 : Nat := 118140960795 + 1147592 * 2 ^ 59
def prefixEnd_1147592 : Nat := 4983230072969 + 3 ^ 40 * 1147592 * 2
def baseEnd_1147592 : Nat := 392844194169719516481551

theorem tailTrace_1147592 : CollatzResearch.WordTrace tailWord_1147592 prefixEnd_1147592 392844194169719516481551 := by
  unfold tailWord_1147592
  simp only [CollatzResearch.WordTrace]
  refine ⟨20928059429238825977450515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27904079238985101303267353 20928059429238825977450515)
  ·
    refine ⟨31392089143858238966175773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20928059429238825977450515 31392089143858238966175773)
    ·
      refine ⟨11772033428946839612315915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31392089143858238966175773 11772033428946839612315915)
      ·
        refine ⟨17658050143420259418473873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11772033428946839612315915 17658050143420259418473873)
        ·
          refine ⟨13243537607565194563855405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17658050143420259418473873 13243537607565194563855405)
          ·
            refine ⟨4966326602836947961445777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13243537607565194563855405 4966326602836947961445777)
            ·
              refine ⟨3724744952127710971084333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4966326602836947961445777 3724744952127710971084333)
              ·
                refine ⟨1396779357047891614156625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3724744952127710971084333 1396779357047891614156625)
                ·
                  refine ⟨1047584517785918710617469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1396779357047891614156625 1047584517785918710617469)
                  ·
                    refine ⟨392844194169719516481551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1047584517785918710617469 392844194169719516481551)
                    ·
                      rfl

theorem cell22_1147592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_1147592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147592 prefixEnd_1147592 := by exact prefixLift 1147592
  have htrace : WordTrace (prefixWord ++ tailWord_1147592) baseStart_1147592 baseEnd_1147592 := by
    simpa [prefixWord, tailWord_1147592, baseEnd_1147592] using wordTrace_append hprefix tailTrace_1147592
  have hstable : (prefixWord ++ tailWord_1147592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147592).length < 2 ^ (prefixWord ++ tailWord_1147592).sum := by decide
  have hdescent : baseEnd_1147592 < baseStart_1147592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147607 : List Nat := [1, 1, 3, 2, 1, 6, 1, 1, 2, 4]
def baseStart_1147607 : Nat := 118140960795 + 1147607 * 2 ^ 59
def prefixEnd_1147607 : Nat := 4983230072969 + 3 ^ 40 * 1147607 * 2
def baseEnd_1147607 : Nat := 392849328976264477356505

theorem tailTrace_1147607 : CollatzResearch.WordTrace tailWord_1147607 prefixEnd_1147607 392849328976264477356505 := by
  unfold tailWord_1147607
  simp only [CollatzResearch.WordTrace]
  refine ⟨41856665953423309516697075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27904443968948873011131383 41856665953423309516697075)
  ·
    refine ⟨62784998930134964275045613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41856665953423309516697075 62784998930134964275045613)
    ·
      refine ⟨23544374598800611603142105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62784998930134964275045613 23544374598800611603142105)
      ·
        refine ⟨17658280949100458702356579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23544374598800611603142105 17658280949100458702356579)
        ·
          refine ⟨26487421423650688053534869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17658280949100458702356579 26487421423650688053534869)
          ·
            refine ⟨1241597879233626002509447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26487421423650688053534869 1241597879233626002509447)
            ·
              refine ⟨1862396818850439003764171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1241597879233626002509447 1862396818850439003764171)
              ·
                refine ⟨2793595228275658505646257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1862396818850439003764171 2793595228275658505646257)
                ·
                  refine ⟨2095196421206743879234693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2793595228275658505646257 2095196421206743879234693)
                  ·
                    refine ⟨392849328976264477356505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2095196421206743879234693 392849328976264477356505)
                    ·
                      rfl

theorem cell22_1147607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_1147607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147607 prefixEnd_1147607 := by exact prefixLift 1147607
  have htrace : WordTrace (prefixWord ++ tailWord_1147607) baseStart_1147607 baseEnd_1147607 := by
    simpa [prefixWord, tailWord_1147607, baseEnd_1147607] using wordTrace_append hprefix tailTrace_1147607
  have hstable : (prefixWord ++ tailWord_1147607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147607).length < 2 ^ (prefixWord ++ tailWord_1147607).sum := by decide
  have hdescent : baseEnd_1147607 < baseStart_1147607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147744 : List Nat := [2, 1, 1, 3, 3, 1, 4, 2, 2, 3]
def baseStart_1147744 : Nat := 118140960795 + 1147744 * 2 ^ 59
def prefixEnd_1147744 : Nat := 4983230072969 + 3 ^ 40 * 1147744 * 2
def baseEnd_1147744 : Nat := 392896226876041786681085

theorem tailTrace_1147744 : CollatzResearch.WordTrace tailWord_1147744 prefixEnd_1147744 392896226876041786681085 := by
  unfold tailWord_1147744
  simp only [CollatzResearch.WordTrace]
  refine ⟨20930831376963490957217143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27907775169284654609622857 20930831376963490957217143)
  ·
    refine ⟨31396247065445236435825715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20930831376963490957217143 31396247065445236435825715)
    ·
      refine ⟨47094370598167854653738573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31396247065445236435825715 47094370598167854653738573)
      ·
        refine ⟨17660388974312945495151965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47094370598167854653738573 17660388974312945495151965)
        ·
          refine ⟨6622645865367354560681987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17660388974312945495151965 6622645865367354560681987)
          ·
            refine ⟨9933968798051031841022981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6622645865367354560681987 9933968798051031841022981)
            ·
              refine ⟨1862619149634568470191809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9933968798051031841022981 1862619149634568470191809)
              ·
                refine ⟨1396964362225926352643857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1862619149634568470191809 1396964362225926352643857)
                ·
                  refine ⟨1047723271669444764482893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1396964362225926352643857 1047723271669444764482893)
                  ·
                    refine ⟨392896226876041786681085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1047723271669444764482893 392896226876041786681085)
                    ·
                      rfl

theorem cell22_1147744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 2, 3].length) (baseStart_1147744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147744 prefixEnd_1147744 := by exact prefixLift 1147744
  have htrace : WordTrace (prefixWord ++ tailWord_1147744) baseStart_1147744 baseEnd_1147744 := by
    simpa [prefixWord, tailWord_1147744, baseEnd_1147744] using wordTrace_append hprefix tailTrace_1147744
  have hstable : (prefixWord ++ tailWord_1147744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147744).length < 2 ^ (prefixWord ++ tailWord_1147744).sum := by decide
  have hdescent : baseEnd_1147744 < baseStart_1147744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147746 : List Nat := [3, 3, 2, 1, 3, 1, 1, 4, 4]
def baseStart_1147746 : Nat := 118140960795 + 1147746 * 2 ^ 59
def prefixEnd_1147746 : Nat := 4983230072969 + 3 ^ 40 * 1147746 * 2
def baseEnd_1147746 : Nat := 130965637172304816043693

theorem tailTrace_1147746 : CollatzResearch.WordTrace tailWord_1147746 prefixEnd_1147746 130965637172304816043693 := by
  unfold tailWord_1147746
  simp only [CollatzResearch.WordTrace]
  refine ⟨10465433924979934064001773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27907823799946490837338061 10465433924979934064001773)
  ·
    refine ⟨3924537721867475274000665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10465433924979934064001773 3924537721867475274000665)
    ·
      refine ⟨2943403291400606455500499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3924537721867475274000665 2943403291400606455500499)
      ·
        refine ⟨4415104937100909683250749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2943403291400606455500499 4415104937100909683250749)
        ·
          refine ⟨1655664351412841131219031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4415104937100909683250749 1655664351412841131219031)
          ·
            refine ⟨2483496527119261696828547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1655664351412841131219031 2483496527119261696828547)
            ·
              refine ⟨3725244790678892545242821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2483496527119261696828547 3725244790678892545242821)
              ·
                refine ⟨698483398252292352233029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3725244790678892545242821 698483398252292352233029)
                ·
                  refine ⟨130965637172304816043693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 698483398252292352233029 130965637172304816043693)
                  ·
                    rfl

theorem cell22_1147746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_1147746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147746 prefixEnd_1147746 := by exact prefixLift 1147746
  have htrace : WordTrace (prefixWord ++ tailWord_1147746) baseStart_1147746 baseEnd_1147746 := by
    simpa [prefixWord, tailWord_1147746, baseEnd_1147746] using wordTrace_append hprefix tailTrace_1147746
  have hstable : (prefixWord ++ tailWord_1147746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147746).length < 2 ^ (prefixWord ++ tailWord_1147746).sum := by decide
  have hdescent : baseEnd_1147746 < baseStart_1147746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147770 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 4, 6]
def baseStart_1147770 : Nat := 118140960795 + 1147770 * 2 ^ 59
def prefixEnd_1147770 : Nat := 4983230072969 + 3 ^ 40 * 1147770 * 2
def baseEnd_1147770 : Nat := 392905127207386385531005

theorem tailTrace_1147770 : CollatzResearch.WordTrace tailWord_1147770 prefixEnd_1147770 392905127207386385531005 := by
  unfold tailWord_1147770
  simp only [CollatzResearch.WordTrace]
  refine ⟨10465652762958197088720191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27908407367888525569920509 10465652762958197088720191)
  ·
    refine ⟨15698479144437295633080287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10465652762958197088720191 15698479144437295633080287)
    ·
      refine ⟨23547718716655943449620431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15698479144437295633080287 23547718716655943449620431)
      ·
        refine ⟨35321578074983915174430647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23547718716655943449620431 35321578074983915174430647)
        ·
          refine ⟨52982367112475872761645971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35321578074983915174430647 52982367112475872761645971)
          ·
            refine ⟨79473550668713809142468957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52982367112475872761645971 79473550668713809142468957)
            ·
              refine ⟨29802581500767678428425859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79473550668713809142468957 29802581500767678428425859)
              ·
                refine ⟨44703872251151517642638789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29802581500767678428425859 44703872251151517642638789)
                ·
                  refine ⟨8381976047090909557994773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44703872251151517642638789 8381976047090909557994773)
                  ·
                    refine ⟨392905127207386385531005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8381976047090909557994773 392905127207386385531005)
                    ·
                      rfl

theorem cell22_1147770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_1147770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147770 prefixEnd_1147770 := by exact prefixLift 1147770
  have htrace : WordTrace (prefixWord ++ tailWord_1147770) baseStart_1147770 baseEnd_1147770 := by
    simpa [prefixWord, tailWord_1147770, baseEnd_1147770] using wordTrace_append hprefix tailTrace_1147770
  have hstable : (prefixWord ++ tailWord_1147770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147770).length < 2 ^ (prefixWord ++ tailWord_1147770).sum := by decide
  have hdescent : baseEnd_1147770 < baseStart_1147770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147864 : List Nat := [2, 1, 2, 2, 2, 5, 1, 1, 6]
def baseStart_1147864 : Nat := 118140960795 + 1147864 * 2 ^ 59
def prefixEnd_1147864 : Nat := 4983230072969 + 3 ^ 40 * 1147864 * 2
def baseEnd_1147864 : Nat := 130979101776133824560239

theorem tailTrace_1147864 : CollatzResearch.WordTrace tailWord_1147864 prefixEnd_1147864 130979101776133824560239 := by
  unfold tailWord_1147864
  simp only [CollatzResearch.WordTrace]
  refine ⟨20933019756746121204401323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27910693008994828272535097 20933019756746121204401323)
  ·
    refine ⟨31399529635119181806601985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20933019756746121204401323 31399529635119181806601985)
    ·
      refine ⟨23549647226339386354951489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31399529635119181806601985 23549647226339386354951489)
      ·
        refine ⟨17662235419754539766213617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23549647226339386354951489 17662235419754539766213617)
        ·
          refine ⟨13246676564815904824660213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17662235419754539766213617 13246676564815904824660213)
          ·
            refine ⟨1241875927951491077311895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13246676564815904824660213 1241875927951491077311895)
            ·
              refine ⟨1862813891927236615967843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1241875927951491077311895 1862813891927236615967843)
              ·
                refine ⟨2794220837890854923951765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1862813891927236615967843 2794220837890854923951765)
                ·
                  refine ⟨130979101776133824560239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2794220837890854923951765 130979101776133824560239)
                  ·
                    rfl

theorem cell22_1147864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 6].length) (baseStart_1147864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147864 prefixEnd_1147864 := by exact prefixLift 1147864
  have htrace : WordTrace (prefixWord ++ tailWord_1147864) baseStart_1147864 baseEnd_1147864 := by
    simpa [prefixWord, tailWord_1147864, baseEnd_1147864] using wordTrace_append hprefix tailTrace_1147864
  have hstable : (prefixWord ++ tailWord_1147864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147864).length < 2 ^ (prefixWord ++ tailWord_1147864).sum := by decide
  have hdescent : baseEnd_1147864 < baseStart_1147864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147952 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 1, 7]
def baseStart_1147952 : Nat := 118140960795 + 1147952 * 2 ^ 59
def prefixEnd_1147952 : Nat := 4983230072969 + 3 ^ 40 * 1147952 * 2
def baseEnd_1147952 : Nat := 392967429526798577480447

theorem tailTrace_1147952 : CollatzResearch.WordTrace tailWord_1147952 prefixEnd_1147952 392967429526798577480447 := by
  unfold tailWord_1147952
  simp only [CollatzResearch.WordTrace]
  refine ⟨20934624568586716719003055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27912832758115622292004073 20934624568586716719003055)
  ·
    refine ⟨31401936852880075078504583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20934624568586716719003055 31401936852880075078504583)
    ·
      refine ⟨47102905279320112617756875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31401936852880075078504583 47102905279320112617756875)
      ·
        refine ⟨70654357918980168926635313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47102905279320112617756875 70654357918980168926635313)
        ·
          refine ⟨52990768439235126694976485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70654357918980168926635313 52990768439235126694976485)
          ·
            refine ⟨9935769082356586255308091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52990768439235126694976485 9935769082356586255308091)
            ·
              refine ⟨14903653623534879382962137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9935769082356586255308091 14903653623534879382962137)
              ·
                refine ⟨11177740217651159537221603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14903653623534879382962137 11177740217651159537221603)
                ·
                  refine ⟨16766610326476739305832405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11177740217651159537221603 16766610326476739305832405)
                  ·
                    refine ⟨392967429526798577480447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16766610326476739305832405 392967429526798577480447)
                    ·
                      rfl

theorem cell22_1147952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_1147952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1147952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1147952 prefixEnd_1147952 := by exact prefixLift 1147952
  have htrace : WordTrace (prefixWord ++ tailWord_1147952) baseStart_1147952 baseEnd_1147952 := by
    simpa [prefixWord, tailWord_1147952, baseEnd_1147952] using wordTrace_append hprefix tailTrace_1147952
  have hstable : (prefixWord ++ tailWord_1147952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147952).length < 2 ^ (prefixWord ++ tailWord_1147952).sum := by decide
  have hdescent : baseEnd_1147952 < baseStart_1147952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148063 : List Nat := [1, 1, 2, 6, 2, 1, 2, 1, 2, 4]
def baseStart_1148063 : Nat := 118140960795 + 1148063 * 2 ^ 59
def prefixEnd_1148063 : Nat := 4983230072969 + 3 ^ 40 * 1148063 * 2
def baseEnd_1148063 : Nat := 393005427095231287955107

theorem tailTrace_1148063 : CollatzResearch.WordTrace tailWord_1148063 prefixEnd_1148063 393005427095231287955107 := by
  unfold tailWord_1148063
  simp only [CollatzResearch.WordTrace]
  refine ⟨41873297639771299395296843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27915531759847532930197895 41873297639771299395296843)
  ·
    refine ⟨62809946459656949092945265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41873297639771299395296843 62809946459656949092945265)
    ·
      refine ⟨47107459844742711819708949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62809946459656949092945265 47107459844742711819708949)
      ·
        refine ⟨2208162180222314616548857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47107459844742711819708949 2208162180222314616548857)
        ·
          refine ⟨1656121635166735962411643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2208162180222314616548857 1656121635166735962411643)
          ·
            refine ⟨2484182452750103943617465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1656121635166735962411643 2484182452750103943617465)
            ·
              refine ⟨1863136839562577957713099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2484182452750103943617465 1863136839562577957713099)
              ·
                refine ⟨2794705259343866936569649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1863136839562577957713099 2794705259343866936569649)
                ·
                  refine ⟨2096028944507900202427237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2794705259343866936569649 2096028944507900202427237)
                  ·
                    refine ⟨393005427095231287955107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2096028944507900202427237 393005427095231287955107)
                    ·
                      rfl

theorem cell22_1148063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 4].length) (baseStart_1148063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148063 prefixEnd_1148063 := by exact prefixLift 1148063
  have htrace : WordTrace (prefixWord ++ tailWord_1148063) baseStart_1148063 baseEnd_1148063 := by
    simpa [prefixWord, tailWord_1148063, baseEnd_1148063] using wordTrace_append hprefix tailTrace_1148063
  have hstable : (prefixWord ++ tailWord_1148063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148063).length < 2 ^ (prefixWord ++ tailWord_1148063).sum := by decide
  have hdescent : baseEnd_1148063 < baseStart_1148063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148104 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 1, 7]
def baseStart_1148104 : Nat := 118140960795 + 1148104 * 2 ^ 59
def prefixEnd_1148104 : Nat := 4983230072969 + 3 ^ 40 * 1148104 * 2
def baseEnd_1148104 : Nat := 393019462233120847679981

theorem tailTrace_1148104 : CollatzResearch.WordTrace tailWord_1148104 prefixEnd_1148104 393019462233120847679981 := by
  unfold tailWord_1148104
  simp only [CollatzResearch.WordTrace]
  refine ⟨20937396516311381698769683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27916528688415175598359577 20937396516311381698769683)
  ·
    refine ⟨31406094774467072548154525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20937396516311381698769683 31406094774467072548154525)
    ·
      refine ⟨11777285540425152205557947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31406094774467072548154525 11777285540425152205557947)
      ·
        refine ⟨17665928310637728308336921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11777285540425152205557947 17665928310637728308336921)
        ·
          refine ⟨13249446232978296231252691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17665928310637728308336921 13249446232978296231252691)
          ·
            refine ⟨19874169349467444346879037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13249446232978296231252691 19874169349467444346879037)
            ·
              refine ⟨7452813506050291630079639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19874169349467444346879037 7452813506050291630079639)
              ·
                refine ⟨11179220259075437445119459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7452813506050291630079639 11179220259075437445119459)
                ·
                  refine ⟨16768830388613156167679189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11179220259075437445119459 16768830388613156167679189)
                  ·
                    refine ⟨393019462233120847679981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16768830388613156167679189 393019462233120847679981)
                    ·
                      rfl

theorem cell22_1148104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_1148104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148104 prefixEnd_1148104 := by exact prefixLift 1148104
  have htrace : WordTrace (prefixWord ++ tailWord_1148104) baseStart_1148104 baseEnd_1148104 := by
    simpa [prefixWord, tailWord_1148104, baseEnd_1148104] using wordTrace_append hprefix tailTrace_1148104
  have hstable : (prefixWord ++ tailWord_1148104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148104).length < 2 ^ (prefixWord ++ tailWord_1148104).sum := by decide
  have hdescent : baseEnd_1148104 < baseStart_1148104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148106 : List Nat := [3, 1, 2, 1, 3, 2, 2, 3, 5]
def baseStart_1148106 : Nat := 118140960795 + 1148106 * 2 ^ 59
def prefixEnd_1148106 : Nat := 4983230072969 + 3 ^ 40 * 1148106 * 2
def baseEnd_1148106 : Nat := 131006715624664503043325

theorem tailTrace_1148106 : CollatzResearch.WordTrace tailWord_1148106 prefixEnd_1148106 131006715624664503043325 := by
  unfold tailWord_1148106
  simp only [CollatzResearch.WordTrace]
  refine ⟨10468716494653879434778043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27916577319077011826074781 10468716494653879434778043)
  ·
    refine ⟨15703074741980819152167065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10468716494653879434778043 15703074741980819152167065)
    ·
      refine ⟨11777306056485614364125299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15703074741980819152167065 11777306056485614364125299)
      ·
        refine ⟨17665959084728421546187949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11777306056485614364125299 17665959084728421546187949)
        ·
          refine ⟨6624734656773158079820481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17665959084728421546187949 6624734656773158079820481)
          ·
            refine ⟨4968550992579868559865361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6624734656773158079820481 4968550992579868559865361)
            ·
              refine ⟨3726413244434901419899021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4968550992579868559865361 3726413244434901419899021)
              ·
                refine ⟨1397404966663088032462133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3726413244434901419899021 1397404966663088032462133)
                ·
                  refine ⟨131006715624664503043325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1397404966663088032462133 131006715624664503043325)
                  ·
                    rfl

theorem cell22_1148106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_1148106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148106 prefixEnd_1148106 := by exact prefixLift 1148106
  have htrace : WordTrace (prefixWord ++ tailWord_1148106) baseStart_1148106 baseEnd_1148106 := by
    simpa [prefixWord, tailWord_1148106, baseEnd_1148106] using wordTrace_append hprefix tailTrace_1148106
  have hstable : (prefixWord ++ tailWord_1148106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148106).length < 2 ^ (prefixWord ++ tailWord_1148106).sum := by decide
  have hdescent : baseEnd_1148106 < baseStart_1148106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148181 : List Nat := [1, 3, 2, 1, 2, 1, 1, 5, 2, 4]
def baseStart_1148181 : Nat := 118140960795 + 1148181 * 2 ^ 59
def prefixEnd_1148181 : Nat := 4983230072969 + 3 ^ 40 * 1148181 * 2
def baseEnd_1148181 : Nat := 393045820906718313504745

theorem tailTrace_1148181 : CollatzResearch.WordTrace tailWord_1148181 prefixEnd_1148181 393045820906718313504745 := by
  unfold tailWord_1148181
  simp only [CollatzResearch.WordTrace]
  refine ⟨41877601453343805548092397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27918400968895870365394931 41877601453343805548092397)
  ·
    refine ⟨15704100545003927080534649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41877601453343805548092397 15704100545003927080534649)
    ·
      refine ⟨11778075408752945310400987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15704100545003927080534649 11778075408752945310400987)
      ·
        refine ⟨17667113113129417965601481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11778075408752945310400987 17667113113129417965601481)
        ·
          refine ⟨13250334834847063474201111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17667113113129417965601481 13250334834847063474201111)
          ·
            refine ⟨19875502252270595211301667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13250334834847063474201111 19875502252270595211301667)
            ·
              refine ⟨29813253378405892816952501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19875502252270595211301667 29813253378405892816952501)
              ·
                refine ⟨2794992504225552451589297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29813253378405892816952501 2794992504225552451589297)
                ·
                  refine ⟨2096244378169164338691973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2794992504225552451589297 2096244378169164338691973)
                  ·
                    refine ⟨393045820906718313504745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2096244378169164338691973 393045820906718313504745)
                    ·
                      rfl

theorem cell22_1148181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_1148181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148181 prefixEnd_1148181 := by exact prefixLift 1148181
  have htrace : WordTrace (prefixWord ++ tailWord_1148181) baseStart_1148181 baseEnd_1148181 := by
    simpa [prefixWord, tailWord_1148181, baseEnd_1148181] using wordTrace_append hprefix tailTrace_1148181
  have hstable : (prefixWord ++ tailWord_1148181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148181).length < 2 ^ (prefixWord ++ tailWord_1148181).sum := by decide
  have hdescent : baseEnd_1148181 < baseStart_1148181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148202 : List Nat := [3, 1, 4, 2, 1, 2, 3, 2, 4]
def baseStart_1148202 : Nat := 118140960795 + 1148202 * 2 ^ 59
def prefixEnd_1148202 : Nat := 4983230072969 + 3 ^ 40 * 1148202 * 2
def baseEnd_1148202 : Nat := 131017669878627086243227

theorem tailTrace_1148202 : CollatzResearch.WordTrace tailWord_1148202 prefixEnd_1148202 131017669878627086243227 := by
  unfold tailWord_1148202
  simp only [CollatzResearch.WordTrace]
  refine ⟨10469591846566931533651715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27918911590845150756404573 10469591846566931533651715)
  ·
    refine ⟨15704387769850397300477573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10469591846566931533651715 15704387769850397300477573)
    ·
      refine ⟨2944572706846949493839545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15704387769850397300477573 2944572706846949493839545)
      ·
        refine ⟨2208429530135212120379659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2944572706846949493839545 2208429530135212120379659)
        ·
          refine ⟨3312644295202818180569489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2208429530135212120379659 3312644295202818180569489)
          ·
            refine ⟨2484483221402113635427117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3312644295202818180569489 2484483221402113635427117)
            ·
              refine ⟨931681208025792613285169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2484483221402113635427117 931681208025792613285169)
              ·
                refine ⟨698760906019344459963877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 931681208025792613285169 698760906019344459963877)
                ·
                  refine ⟨131017669878627086243227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 698760906019344459963877 131017669878627086243227)
                  ·
                    rfl

theorem cell22_1148202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 4].length) (baseStart_1148202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148202 prefixEnd_1148202 := by exact prefixLift 1148202
  have htrace : WordTrace (prefixWord ++ tailWord_1148202) baseStart_1148202 baseEnd_1148202 := by
    simpa [prefixWord, tailWord_1148202, baseEnd_1148202] using wordTrace_append hprefix tailTrace_1148202
  have hstable : (prefixWord ++ tailWord_1148202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148202).length < 2 ^ (prefixWord ++ tailWord_1148202).sum := by decide
  have hdescent : baseEnd_1148202 < baseStart_1148202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148253 : List Nat := [1, 4, 5, 1, 2, 1, 2, 2, 4]
def baseStart_1148253 : Nat := 118140960795 + 1148253 * 2 ^ 59
def prefixEnd_1148253 : Nat := 4983230072969 + 3 ^ 40 * 1148253 * 2
def baseEnd_1148253 : Nat := 131023489326044708568175

theorem tailTrace_1148253 : CollatzResearch.WordTrace tailWord_1148253 prefixEnd_1148253 131023489326044708568175 := by
  unfold tailWord_1148253
  simp only [CollatzResearch.WordTrace]
  refine ⟨41880227509082961844713413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27920151672721974563142275 41880227509082961844713413)
  ·
    refine ⟨7852542657953055345883765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41880227509082961844713413 7852542657953055345883765)
    ·
      refine ⟨736175874183098938676603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7852542657953055345883765 736175874183098938676603)
      ·
        refine ⟨1104263811274648408014905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736175874183098938676603 1104263811274648408014905)
        ·
          refine ⟨828197858455986306011179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1104263811274648408014905 828197858455986306011179)
          ·
            refine ⟨1242296787683979459016769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828197858455986306011179 1242296787683979459016769)
            ·
              refine ⟨931722590762984594262577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1242296787683979459016769 931722590762984594262577)
              ·
                refine ⟨698791943072238445696933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 931722590762984594262577 698791943072238445696933)
                ·
                  refine ⟨131023489326044708568175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 698791943072238445696933 131023489326044708568175)
                  ·
                    rfl

theorem cell22_1148253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_1148253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148253 prefixEnd_1148253 := by exact prefixLift 1148253
  have htrace : WordTrace (prefixWord ++ tailWord_1148253) baseStart_1148253 baseEnd_1148253 := by
    simpa [prefixWord, tailWord_1148253, baseEnd_1148253] using wordTrace_append hprefix tailTrace_1148253
  have hstable : (prefixWord ++ tailWord_1148253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148253).length < 2 ^ (prefixWord ++ tailWord_1148253).sum := by decide
  have hdescent : baseEnd_1148253 < baseStart_1148253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148271 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 5, 4]
def baseStart_1148271 : Nat := 118140960795 + 1148271 * 2 ^ 59
def prefixEnd_1148271 : Nat := 4983230072969 + 3 ^ 40 * 1148271 * 2
def baseEnd_1148271 : Nat := 393076629745988078754469

theorem tailTrace_1148271 : CollatzResearch.WordTrace tailWord_1148271 prefixEnd_1148271 393076629745988078754469 := by
  unfold tailWord_1148271
  simp only [CollatzResearch.WordTrace]
  refine ⟨41880884023017750918868667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27920589348678500612579111 41880884023017750918868667)
  ·
    refine ⟨62821326034526626378303001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41880884023017750918868667 62821326034526626378303001)
    ·
      refine ⟨47115994525894969783727251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62821326034526626378303001 47115994525894969783727251)
      ·
        refine ⟨70673991788842454675590877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47115994525894969783727251 70673991788842454675590877)
        ·
          refine ⟨26502746920815920503346579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70673991788842454675590877 26502746920815920503346579)
          ·
            refine ⟨39754120381223880755019869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26502746920815920503346579 39754120381223880755019869)
            ·
              refine ⟨14907795142958955283132451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39754120381223880755019869 14907795142958955283132451)
              ·
                refine ⟨22361692714438432924698677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14907795142958955283132451 22361692714438432924698677)
                ·
                  refine ⟨2096408691978603086690501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22361692714438432924698677 2096408691978603086690501)
                  ·
                    refine ⟨393076629745988078754469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2096408691978603086690501 393076629745988078754469)
                    ·
                      rfl

theorem cell22_1148271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 4].length) (baseStart_1148271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148271 prefixEnd_1148271 := by exact prefixLift 1148271
  have htrace : WordTrace (prefixWord ++ tailWord_1148271) baseStart_1148271 baseEnd_1148271 := by
    simpa [prefixWord, tailWord_1148271, baseEnd_1148271] using wordTrace_append hprefix tailTrace_1148271
  have hstable : (prefixWord ++ tailWord_1148271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148271).length < 2 ^ (prefixWord ++ tailWord_1148271).sum := by decide
  have hdescent : baseEnd_1148271 < baseStart_1148271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148361 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 1, 8]
def baseStart_1148361 : Nat := 118140960795 + 1148361 * 2 ^ 59
def prefixEnd_1148361 : Nat := 4983230072969 + 3 ^ 40 * 1148361 * 2
def baseEnd_1148361 : Nat := 393107438585257844004193

theorem tailTrace_1148361 : CollatzResearch.WordTrace tailWord_1148361 prefixEnd_1148361 393107438585257844004193 := by
  unfold tailWord_1148361
  simp only [CollatzResearch.WordTrace]
  refine ⟨41884166592691696289644937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27922777728461130859763291 41884166592691696289644937)
  ·
    refine ⟨31413124944518772217233703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41884166592691696289644937 31413124944518772217233703)
    ·
      refine ⟨47119687416778158325850555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31413124944518772217233703 47119687416778158325850555)
      ·
        refine ⟨70679531125167237488775833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47119687416778158325850555 70679531125167237488775833)
        ·
          refine ⟨53009648343875428116581875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70679531125167237488775833 53009648343875428116581875)
          ·
            refine ⟨79514472515813142174872813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53009648343875428116581875 79514472515813142174872813)
            ·
              refine ⟨29817927193429928315577305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79514472515813142174872813 29817927193429928315577305)
              ·
                refine ⟨22363445395072446236682979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29817927193429928315577305 22363445395072446236682979)
                ·
                  refine ⟨33545168092608669355024469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22363445395072446236682979 33545168092608669355024469)
                  ·
                    refine ⟨393107438585257844004193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33545168092608669355024469 393107438585257844004193)
                    ·
                      rfl

theorem cell22_1148361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_1148361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148361 prefixEnd_1148361 := by exact prefixLift 1148361
  have htrace : WordTrace (prefixWord ++ tailWord_1148361) baseStart_1148361 baseEnd_1148361 := by
    simpa [prefixWord, tailWord_1148361, baseEnd_1148361] using wordTrace_append hprefix tailTrace_1148361
  have hstable : (prefixWord ++ tailWord_1148361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148361).length < 2 ^ (prefixWord ++ tailWord_1148361).sum := by decide
  have hdescent : baseEnd_1148361 < baseStart_1148361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148363 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 5, 3]
def baseStart_1148363 : Nat := 118140960795 + 1148363 * 2 ^ 59
def prefixEnd_1148363 : Nat := 4983230072969 + 3 ^ 40 * 1148363 * 2
def baseEnd_1148363 : Nat := 393108123226130505454187

theorem tailTrace_1148363 : CollatzResearch.WordTrace tailWord_1148363 prefixEnd_1148363 393108123226130505454187 := by
  unfold tailWord_1148363
  simp only [CollatzResearch.WordTrace]
  refine ⟨41884239538684450631217743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27922826359122967087478495 41884239538684450631217743)
  ·
    refine ⟨62826359308026675946826615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41884239538684450631217743 62826359308026675946826615)
    ·
      refine ⟨94239538962040013920239923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62826359308026675946826615 94239538962040013920239923)
      ·
        refine ⟨141359308443060020880359885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94239538962040013920239923 141359308443060020880359885)
        ·
          refine ⟨53009740666147507830134957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141359308443060020880359885 53009740666147507830134957)
          ·
            refine ⟨19878652749805315436300609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53009740666147507830134957 19878652749805315436300609)
            ·
              refine ⟨14908989562353986577225457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19878652749805315436300609 14908989562353986577225457)
              ·
                refine ⟨11181742171765489932919093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14908989562353986577225457 11181742171765489932919093)
                ·
                  refine ⟨1048288328603014681211165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11181742171765489932919093 1048288328603014681211165)
                  ·
                    refine ⟨393108123226130505454187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1048288328603014681211165 393108123226130505454187)
                    ·
                      rfl

theorem cell22_1148363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 3].length) (baseStart_1148363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148363 prefixEnd_1148363 := by exact prefixLift 1148363
  have htrace : WordTrace (prefixWord ++ tailWord_1148363) baseStart_1148363 baseEnd_1148363 := by
    simpa [prefixWord, tailWord_1148363, baseEnd_1148363] using wordTrace_append hprefix tailTrace_1148363
  have hstable : (prefixWord ++ tailWord_1148363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148363).length < 2 ^ (prefixWord ++ tailWord_1148363).sum := by decide
  have hdescent : baseEnd_1148363 < baseStart_1148363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148472 : List Nat := [2, 1, 2, 1, 4, 3, 2, 3, 4]
def baseStart_1148472 : Nat := 118140960795 + 1148472 * 2 ^ 59
def prefixEnd_1148472 : Nat := 4983230072969 + 3 ^ 40 * 1148472 * 2
def baseEnd_1148472 : Nat := 131048478717896851492951

theorem tailTrace_1148472 : CollatzResearch.WordTrace tailWord_1148472 prefixEnd_1148472 131048478717896851492951 := by
  unfold tailWord_1148472
  simp only [CollatzResearch.WordTrace]
  refine ⟨20944107547644781123467835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27925476730193041497957113 20944107547644781123467835)
  ·
    refine ⟨31416161321467171685201753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20944107547644781123467835 31416161321467171685201753)
    ·
      refine ⟨23562120991100378763901315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31416161321467171685201753 23562120991100378763901315)
      ·
        refine ⟨35343181486650568145851973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23562120991100378763901315 35343181486650568145851973)
        ·
          refine ⟨6626846528746981527347245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35343181486650568145851973 6626846528746981527347245)
          ·
            refine ⟨2485067448280118072755217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6626846528746981527347245 2485067448280118072755217)
            ·
              refine ⟨1863800586210088554566413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2485067448280118072755217 1863800586210088554566413)
              ·
                refine ⟨698925219828783207962405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1863800586210088554566413 698925219828783207962405)
                ·
                  refine ⟨131048478717896851492951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 698925219828783207962405 131048478717896851492951)
                  ·
                    rfl

theorem cell22_1148472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 4].length) (baseStart_1148472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148472 prefixEnd_1148472 := by exact prefixLift 1148472
  have htrace : WordTrace (prefixWord ++ tailWord_1148472) baseStart_1148472 baseEnd_1148472 := by
    simpa [prefixWord, tailWord_1148472, baseEnd_1148472] using wordTrace_append hprefix tailTrace_1148472
  have hstable : (prefixWord ++ tailWord_1148472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148472).length < 2 ^ (prefixWord ++ tailWord_1148472).sum := by decide
  have hdescent : baseEnd_1148472 < baseStart_1148472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148487 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 4, 3]
def baseStart_1148487 : Nat := 118140960795 + 1148487 * 2 ^ 59
def prefixEnd_1148487 : Nat := 4983230072969 + 3 ^ 40 * 1148487 * 2
def baseEnd_1148487 : Nat := 393150570960235515353807

theorem tailTrace_1148487 : CollatzResearch.WordTrace tailWord_1148487 prefixEnd_1148487 393150570960235515353807 := by
  unfold tailWord_1148487
  simp only [CollatzResearch.WordTrace]
  refine ⟨41888762190235219808731715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27925841460156813205821143 41888762190235219808731715)
  ·
    refine ⟨62833143285352829713097573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41888762190235219808731715 62833143285352829713097573)
    ·
      refine ⟨11781214366003655571205795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62833143285352829713097573 11781214366003655571205795)
      ·
        refine ⟨17671821549005483356808693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11781214366003655571205795 17671821549005483356808693)
        ·
          refine ⟨1656733270219264064700815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17671821549005483356808693 1656733270219264064700815)
          ·
            refine ⟨2485099905328896097051223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1656733270219264064700815 2485099905328896097051223)
            ·
              refine ⟨3727649857993344145576835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2485099905328896097051223 3727649857993344145576835)
              ·
                refine ⟨5591474786990016218365253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3727649857993344145576835 5591474786990016218365253)
                ·
                  refine ⟨1048401522560628040943485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5591474786990016218365253 1048401522560628040943485)
                  ·
                    refine ⟨393150570960235515353807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1048401522560628040943485 393150570960235515353807)
                    ·
                      rfl

theorem cell22_1148487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_1148487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148487 prefixEnd_1148487 := by exact prefixLift 1148487
  have htrace : WordTrace (prefixWord ++ tailWord_1148487) baseStart_1148487 baseEnd_1148487 := by
    simpa [prefixWord, tailWord_1148487, baseEnd_1148487] using wordTrace_append hprefix tailTrace_1148487
  have hstable : (prefixWord ++ tailWord_1148487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148487).length < 2 ^ (prefixWord ++ tailWord_1148487).sum := by decide
  have hdescent : baseEnd_1148487 < baseStart_1148487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148517 : List Nat := [1, 3, 1, 3, 3, 3, 2, 6]
def baseStart_1148517 : Nat := 118140960795 + 1148517 * 2 ^ 59
def prefixEnd_1148517 : Nat := 4983230072969 + 3 ^ 40 * 1148517 * 2
def baseEnd_1148517 : Nat := 43684537841480604122635

theorem tailTrace_1148517 : CollatzResearch.WordTrace tailWord_1148517 prefixEnd_1148517 43684537841480604122635 := by
  unfold tailWord_1148517
  simp only [CollatzResearch.WordTrace]
  refine ⟨41889856380126534932323805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27926570920084356621549203 41889856380126534932323805)
  ·
    refine ⟨15708696142547450599621427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41889856380126534932323805 15708696142547450599621427)
    ·
      refine ⟨23563044213821175899432141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15708696142547450599621427 23563044213821175899432141)
      ·
        refine ⟨8836141580182940962287053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23563044213821175899432141 8836141580182940962287053)
        ·
          refine ⟨3313553092568602860857645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8836141580182940962287053 3313553092568602860857645)
          ·
            refine ⟨1242582409713226072821617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3313553092568602860857645 1242582409713226072821617)
            ·
              refine ⟨931936807284919554616213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1242582409713226072821617 931936807284919554616213)
              ·
                refine ⟨43684537841480604122635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 931936807284919554616213 43684537841480604122635)
                ·
                  rfl

theorem cell22_1148517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 6].length) (baseStart_1148517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148517 prefixEnd_1148517 := by exact prefixLift 1148517
  have htrace : WordTrace (prefixWord ++ tailWord_1148517) baseStart_1148517 baseEnd_1148517 := by
    simpa [prefixWord, tailWord_1148517, baseEnd_1148517] using wordTrace_append hprefix tailTrace_1148517
  have hstable : (prefixWord ++ tailWord_1148517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148517).length < 2 ^ (prefixWord ++ tailWord_1148517).sum := by decide
  have hdescent : baseEnd_1148517 < baseStart_1148517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148545 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 7]
def baseStart_1148545 : Nat := 118140960795 + 1148545 * 2 ^ 59
def prefixEnd_1148545 : Nat := 4983230072969 + 3 ^ 40 * 1148545 * 2
def baseEnd_1148545 : Nat := 131056808515180899134543

theorem tailTrace_1148545 : CollatzResearch.WordTrace tailWord_1148545 prefixEnd_1148545 131056808515180899134543 := by
  unfold tailWord_1148545
  simp only [CollatzResearch.WordTrace]
  refine ⟨41890877624025095714343089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27927251749350063809562059 41890877624025095714343089)
  ·
    refine ⟨31418158218018821785757317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41890877624025095714343089 31418158218018821785757317)
    ·
      refine ⟨5890904665878529084829497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31418158218018821785757317 5890904665878529084829497)
      ·
        refine ⟨4418178499408896813622123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5890904665878529084829497 4418178499408896813622123)
        ·
          refine ⟨6627267749113345220433185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4418178499408896813622123 6627267749113345220433185)
          ·
            refine ⟨4970450811835008915324889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6627267749113345220433185 4970450811835008915324889)
            ·
              refine ⟨3727838108876256686493667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4970450811835008915324889 3727838108876256686493667)
              ·
                refine ⟨5591757163314385029740501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3727838108876256686493667 5591757163314385029740501)
                ·
                  refine ⟨131056808515180899134543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5591757163314385029740501 131056808515180899134543)
                  ·
                    rfl

theorem cell22_1148545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 7].length) (baseStart_1148545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148545 prefixEnd_1148545 := by exact prefixLift 1148545
  have htrace : WordTrace (prefixWord ++ tailWord_1148545) baseStart_1148545 baseEnd_1148545 := by
    simpa [prefixWord, tailWord_1148545, baseEnd_1148545] using wordTrace_append hprefix tailTrace_1148545
  have hstable : (prefixWord ++ tailWord_1148545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148545).length < 2 ^ (prefixWord ++ tailWord_1148545).sum := by decide
  have hdescent : baseEnd_1148545 < baseStart_1148545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148605 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_1148605 : Nat := 118140960795 + 1148605 * 2 ^ 59
def prefixEnd_1148605 : Nat := 4983230072969 + 3 ^ 40 * 1148605 * 2
def baseEnd_1148605 : Nat := 393190964771722540903445

theorem tailTrace_1148605 : CollatzResearch.WordTrace tailWord_1148605 prefixEnd_1148605 393190964771722540903445 := by
  unfold tailWord_1148605
  simp only [CollatzResearch.WordTrace]
  refine ⟨41893066003807725961527269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27928710669205150641018179 41893066003807725961527269)
  ·
    refine ⟨7854949875713948617786363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41893066003807725961527269 7854949875713948617786363)
    ·
      refine ⟨11782424813570922926679545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7854949875713948617786363 11782424813570922926679545)
      ·
        refine ⟨8836818610178192195009659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11782424813570922926679545 8836818610178192195009659)
        ·
          refine ⟨13255227915267288292514489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8836818610178192195009659 13255227915267288292514489)
          ·
            refine ⟨9941420936450466219385867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13255227915267288292514489 9941420936450466219385867)
            ·
              refine ⟨14912131404675699329078801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9941420936450466219385867 14912131404675699329078801)
              ·
                refine ⟨11184098553506774496809101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14912131404675699329078801 11184098553506774496809101)
                ·
                  refine ⟨4194036957565040436303413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11184098553506774496809101 4194036957565040436303413)
                  ·
                    refine ⟨393190964771722540903445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4194036957565040436303413 393190964771722540903445)
                    ·
                      rfl

theorem cell22_1148605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_1148605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148605 prefixEnd_1148605 := by exact prefixLift 1148605
  have htrace : WordTrace (prefixWord ++ tailWord_1148605) baseStart_1148605 baseEnd_1148605 := by
    simpa [prefixWord, tailWord_1148605, baseEnd_1148605] using wordTrace_append hprefix tailTrace_1148605
  have hstable : (prefixWord ++ tailWord_1148605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148605).length < 2 ^ (prefixWord ++ tailWord_1148605).sum := by decide
  have hdescent : baseEnd_1148605 < baseStart_1148605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148607 : List Nat := [1, 1, 2, 2, 2, 3, 3, 4, 4]
def baseStart_1148607 : Nat := 118140960795 + 1148607 * 2 ^ 59
def prefixEnd_1148607 : Nat := 4983230072969 + 3 ^ 40 * 1148607 * 2
def baseEnd_1148607 : Nat := 131063883137531734117813

theorem tailTrace_1148607 : CollatzResearch.WordTrace tailWord_1148607 prefixEnd_1148607 131063883137531734117813 := by
  unfold tailWord_1148607
  simp only [CollatzResearch.WordTrace]
  refine ⟨41893138949800480303100075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27928759299866986868733383 41893138949800480303100075)
  ·
    refine ⟨62839708424700720454650113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41893138949800480303100075 62839708424700720454650113)
    ·
      refine ⟨47129781318525540340987585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62839708424700720454650113 47129781318525540340987585)
      ·
        refine ⟨35347335988894155255740689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47129781318525540340987585 35347335988894155255740689)
        ·
          refine ⟨26510501991670616441805517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35347335988894155255740689 26510501991670616441805517)
          ·
            refine ⟨9941438246876481165677069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26510501991670616441805517 9941438246876481165677069)
            ·
              refine ⟨3728039342578680437128901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9941438246876481165677069 3728039342578680437128901)
              ·
                refine ⟨699007376733502581961669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3728039342578680437128901 699007376733502581961669)
                ·
                  refine ⟨131063883137531734117813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 699007376733502581961669 131063883137531734117813)
                  ·
                    rfl

theorem cell22_1148607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 4].length) (baseStart_1148607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148607 prefixEnd_1148607 := by exact prefixLift 1148607
  have htrace : WordTrace (prefixWord ++ tailWord_1148607) baseStart_1148607 baseEnd_1148607 := by
    simpa [prefixWord, tailWord_1148607, baseEnd_1148607] using wordTrace_append hprefix tailTrace_1148607
  have hstable : (prefixWord ++ tailWord_1148607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148607).length < 2 ^ (prefixWord ++ tailWord_1148607).sum := by decide
  have hdescent : baseEnd_1148607 < baseStart_1148607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148622 : List Nat := [4, 1, 1, 1, 3, 1, 4, 1, 1, 5]
def baseStart_1148622 : Nat := 118140960795 + 1148622 * 2 ^ 59
def prefixEnd_1148622 : Nat := 4983230072969 + 3 ^ 40 * 1148622 * 2
def baseEnd_1148622 : Nat := 393196784219140163228393

theorem tailTrace_1148622 : CollatzResearch.WordTrace tailWord_1148622 prefixEnd_1148622 393196784219140163228393 := by
  unfold tailWord_1148622
  simp only [CollatzResearch.WordTrace]
  refine ⟨5236710755593267233112015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27929124029830758576597413 5236710755593267233112015)
  ·
    refine ⟨7855066133389900849668023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5236710755593267233112015 7855066133389900849668023)
    ·
      refine ⟨11782599200084851274502035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7855066133389900849668023 11782599200084851274502035)
      ·
        refine ⟨17673898800127276911753053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11782599200084851274502035 17673898800127276911753053)
        ·
          refine ⟨6627712050047728841907395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17673898800127276911753053 6627712050047728841907395)
          ·
            refine ⟨9941568075071593262861093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6627712050047728841907395 9941568075071593262861093)
            ·
              refine ⟨1864044014075923736786455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9941568075071593262861093 1864044014075923736786455)
              ·
                refine ⟨2796066021113885605179683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1864044014075923736786455 2796066021113885605179683)
                ·
                  refine ⟨4194099031670828407769525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2796066021113885605179683 4194099031670828407769525)
                  ·
                    refine ⟨393196784219140163228393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4194099031670828407769525 393196784219140163228393)
                    ·
                      rfl

theorem cell22_1148622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_1148622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148622 prefixEnd_1148622 := by exact prefixLift 1148622
  have htrace : WordTrace (prefixWord ++ tailWord_1148622) baseStart_1148622 baseEnd_1148622 := by
    simpa [prefixWord, tailWord_1148622, baseEnd_1148622] using wordTrace_append hprefix tailTrace_1148622
  have hstable : (prefixWord ++ tailWord_1148622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148622).length < 2 ^ (prefixWord ++ tailWord_1148622).sum := by decide
  have hdescent : baseEnd_1148622 < baseStart_1148622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148643 : List Nat := [1, 1, 1, 7, 3, 1, 2, 1, 1, 4]
def baseStart_1148643 : Nat := 118140960795 + 1148643 * 2 ^ 59
def prefixEnd_1148643 : Nat := 4983230072969 + 3 ^ 40 * 1148643 * 2
def baseEnd_1148643 : Nat := 393203972948303108453329

theorem tailTrace_1148643 : CollatzResearch.WordTrace tailWord_1148643 prefixEnd_1148643 393203972948303108453329 := by
  unfold tailWord_1148643
  simp only [CollatzResearch.WordTrace]
  refine ⟨41894451977670058451410583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27929634651780038967607055 41894451977670058451410583)
  ·
    refine ⟨62841677966505087677115875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41894451977670058451410583 62841677966505087677115875)
    ·
      refine ⟨94262516949757631515673813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62841677966505087677115875 94262516949757631515673813)
      ·
        refine ⟨2209277741009944488648605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 94262516949757631515673813 2209277741009944488648605)
        ·
          refine ⟨828479152878729183243227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2209277741009944488648605 828479152878729183243227)
          ·
            refine ⟨1242718729318093774864841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828479152878729183243227 1242718729318093774864841)
            ·
              refine ⟨932039046988570331148631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1242718729318093774864841 932039046988570331148631)
              ·
                refine ⟨1398058570482855496722947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 932039046988570331148631 1398058570482855496722947)
                ·
                  refine ⟨2097087855724283245084421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1398058570482855496722947 2097087855724283245084421)
                  ·
                    refine ⟨393203972948303108453329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2097087855724283245084421 393203972948303108453329)
                    ·
                      rfl

theorem cell22_1148643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 1, 4].length) (baseStart_1148643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148643 prefixEnd_1148643 := by exact prefixLift 1148643
  have htrace : WordTrace (prefixWord ++ tailWord_1148643) baseStart_1148643 baseEnd_1148643 := by
    simpa [prefixWord, tailWord_1148643, baseEnd_1148643] using wordTrace_append hprefix tailTrace_1148643
  have hstable : (prefixWord ++ tailWord_1148643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148643).length < 2 ^ (prefixWord ++ tailWord_1148643).sum := by decide
  have hdescent : baseEnd_1148643 < baseStart_1148643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148692 : List Nat := [2, 4, 4, 1, 2, 1, 1, 3, 4]
def baseStart_1148692 : Nat := 118140960795 + 1148692 * 2 ^ 59
def prefixEnd_1148692 : Nat := 4983230072969 + 3 ^ 40 * 1148692 * 2
def baseEnd_1148692 : Nat := 131073582216561104659393

theorem tailTrace_1148692 : CollatzResearch.WordTrace tailWord_1148692 prefixEnd_1148692 131073582216561104659393 := by
  unfold tailWord_1148692
  simp only [CollatzResearch.WordTrace]
  refine ⟨20948119577246269909972165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27930826102995026546629553 20948119577246269909972165)
  ·
    refine ⟨3927772420733675608119781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20948119577246269909972165 3927772420733675608119781)
    ·
      refine ⟨736457328887564176522459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3927772420733675608119781 736457328887564176522459)
      ·
        refine ⟨1104685993331346264783689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736457328887564176522459 1104685993331346264783689)
        ·
          refine ⟨828514494998509698587767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1104685993331346264783689 828514494998509698587767)
          ·
            refine ⟨1242771742497764547881651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828514494998509698587767 1242771742497764547881651)
            ·
              refine ⟨1864157613746646821822477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1242771742497764547881651 1864157613746646821822477)
              ·
                refine ⟨699059105154992558183429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1864157613746646821822477 699059105154992558183429)
                ·
                  refine ⟨131073582216561104659393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 699059105154992558183429 131073582216561104659393)
                  ·
                    rfl

theorem cell22_1148692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_1148692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148692 prefixEnd_1148692 := by exact prefixLift 1148692
  have htrace : WordTrace (prefixWord ++ tailWord_1148692) baseStart_1148692 baseEnd_1148692 := by
    simpa [prefixWord, tailWord_1148692, baseEnd_1148692] using wordTrace_append hprefix tailTrace_1148692
  have hstable : (prefixWord ++ tailWord_1148692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148692).length < 2 ^ (prefixWord ++ tailWord_1148692).sum := by decide
  have hdescent : baseEnd_1148692 < baseStart_1148692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148718 : List Nat := [4, 1, 3, 2, 2, 2, 1, 1, 3, 3]
def baseStart_1148718 : Nat := 118140960795 + 1148718 * 2 ^ 59
def prefixEnd_1148718 : Nat := 4983230072969 + 3 ^ 40 * 1148718 * 2
def baseEnd_1148718 : Nat := 393229646981027912828099

theorem tailTrace_1148718 : CollatzResearch.WordTrace tailWord_1148718 prefixEnd_1148718 393229646981027912828099 := by
  unfold tailWord_1148718
  simp only [CollatzResearch.WordTrace]
  refine ⟨5237148431549793282548851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27931458301598897506927205 5237148431549793282548851)
  ·
    refine ⟨7855722647324689923823277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5237148431549793282548851 7855722647324689923823277)
    ·
      refine ⟨2945895992746758721433729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7855722647324689923823277 2945895992746758721433729)
      ·
        refine ⟨2209421994560069041075297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2945895992746758721433729 2209421994560069041075297)
        ·
          refine ⟨1657066495920051780806473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2209421994560069041075297 1657066495920051780806473)
          ·
            refine ⟨1242799871940038835604855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1657066495920051780806473 1242799871940038835604855)
            ·
              refine ⟨1864199807910058253407283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1242799871940038835604855 1864199807910058253407283)
              ·
                refine ⟨2796299711865087380110925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1864199807910058253407283 2796299711865087380110925)
                ·
                  refine ⟨1048612391949407767541597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2796299711865087380110925 1048612391949407767541597)
                  ·
                    refine ⟨393229646981027912828099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1048612391949407767541597 393229646981027912828099)
                    ·
                      rfl

theorem cell22_1148718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_1148718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148718 prefixEnd_1148718 := by exact prefixLift 1148718
  have htrace : WordTrace (prefixWord ++ tailWord_1148718) baseStart_1148718 baseEnd_1148718 := by
    simpa [prefixWord, tailWord_1148718, baseEnd_1148718] using wordTrace_append hprefix tailTrace_1148718
  have hstable : (prefixWord ++ tailWord_1148718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148718).length < 2 ^ (prefixWord ++ tailWord_1148718).sum := by decide
  have hdescent : baseEnd_1148718 < baseStart_1148718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148744 : List Nat := [2, 1, 3, 1, 1, 4, 3, 2, 1, 4]
def baseStart_1148744 : Nat := 118140960795 + 1148744 * 2 ^ 59
def prefixEnd_1148744 : Nat := 4983230072969 + 3 ^ 40 * 1148744 * 2
def baseEnd_1148744 : Nat := 393238547312372511678019

theorem tailTrace_1148744 : CollatzResearch.WordTrace tailWord_1148744 prefixEnd_1148744 393238547312372511678019 := by
  unfold tailWord_1148744
  simp only [CollatzResearch.WordTrace]
  refine ⟨20949067875152076350418643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27932090500202768467224857 20949067875152076350418643)
  ·
    refine ⟨31423601812728114525627965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20949067875152076350418643 31423601812728114525627965)
    ·
      refine ⟨11783850679773042947110487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31423601812728114525627965 11783850679773042947110487)
      ·
        refine ⟨17675776019659564420665731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11783850679773042947110487 17675776019659564420665731)
        ·
          refine ⟨26513664029489346630998597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17675776019659564420665731 26513664029489346630998597)
          ·
            refine ⟨4971312005529252493312237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26513664029489346630998597 4971312005529252493312237)
            ·
              refine ⟨1864242002073469684992089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4971312005529252493312237 1864242002073469684992089)
              ·
                refine ⟨1398181501555102263744067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1864242002073469684992089 1398181501555102263744067)
                ·
                  refine ⟨2097272252332653395616101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1398181501555102263744067 2097272252332653395616101)
                  ·
                    refine ⟨393238547312372511678019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2097272252332653395616101 393238547312372511678019)
                    ·
                      rfl

theorem cell22_1148744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_1148744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148744 prefixEnd_1148744 := by exact prefixLift 1148744
  have htrace : WordTrace (prefixWord ++ tailWord_1148744) baseStart_1148744 baseEnd_1148744 := by
    simpa [prefixWord, tailWord_1148744, baseEnd_1148744] using wordTrace_append hprefix tailTrace_1148744
  have hstable : (prefixWord ++ tailWord_1148744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148744).length < 2 ^ (prefixWord ++ tailWord_1148744).sum := by decide
  have hdescent : baseEnd_1148744 < baseStart_1148744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148757 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 3, 5]
def baseStart_1148757 : Nat := 118140960795 + 1148757 * 2 ^ 59
def prefixEnd_1148757 : Nat := 4983230072969 + 3 ^ 40 * 1148757 * 2
def baseEnd_1148757 : Nat := 393242997478044811102979

theorem tailTrace_1148757 : CollatzResearch.WordTrace tailWord_1148757 prefixEnd_1148757 393242997478044811102979 := by
  unfold tailWord_1148757
  simp only [CollatzResearch.WordTrace]
  refine ⟨41898609899257055921060525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27932406599504703947373683 41898609899257055921060525)
  ·
    refine ⟨15711978712221395970397697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41898609899257055921060525 15711978712221395970397697)
    ·
      refine ⟨11783984034166046977798273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15711978712221395970397697 11783984034166046977798273)
      ·
        refine ⟨8837988025624535233348705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11783984034166046977798273 8837988025624535233348705)
        ·
          refine ⟨6628491019218401425011529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8837988025624535233348705 6628491019218401425011529)
          ·
            refine ⟨4971368264413801068758647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6628491019218401425011529 4971368264413801068758647)
            ·
              refine ⟨7457052396620701603137971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4971368264413801068758647 7457052396620701603137971)
              ·
                refine ⟨11185578594931052404706957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7457052396620701603137971 11185578594931052404706957)
                ·
                  refine ⟨4194591973099144651765109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11185578594931052404706957 4194591973099144651765109)
                  ·
                    refine ⟨393242997478044811102979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4194591973099144651765109 393242997478044811102979)
                    ·
                      rfl

theorem cell22_1148757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_1148757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148757 prefixEnd_1148757 := by exact prefixLift 1148757
  have htrace : WordTrace (prefixWord ++ tailWord_1148757) baseStart_1148757 baseEnd_1148757 := by
    simpa [prefixWord, tailWord_1148757, baseEnd_1148757] using wordTrace_append hprefix tailTrace_1148757
  have hstable : (prefixWord ++ tailWord_1148757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148757).length < 2 ^ (prefixWord ++ tailWord_1148757).sum := by decide
  have hdescent : baseEnd_1148757 < baseStart_1148757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148836 : List Nat := [2, 3, 1, 2, 1, 4, 2, 1, 3, 3]
def baseStart_1148836 : Nat := 118140960795 + 1148836 * 2 ^ 59
def prefixEnd_1148836 : Nat := 4983230072969 + 3 ^ 40 * 1148836 * 2
def baseEnd_1148836 : Nat := 393270040792514938377737

theorem tailTrace_1148836 : CollatzResearch.WordTrace tailWord_1148836 prefixEnd_1148836 393270040792514938377737 := by
  unfold tailWord_1148836
  simp only [CollatzResearch.WordTrace]
  refine ⟨20950745632985426206593181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27934327510647234942124241 20950745632985426206593181)
  ·
    refine ⟨7856529612369534827472443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20950745632985426206593181 7856529612369534827472443)
    ·
      refine ⟨11784794418554302241208665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7856529612369534827472443 11784794418554302241208665)
      ·
        refine ⟨8838595813915726680906499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11784794418554302241208665 8838595813915726680906499)
        ·
          refine ⟨13257893720873590021359749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8838595813915726680906499 13257893720873590021359749)
          ·
            refine ⟨2485855072663798129004953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13257893720873590021359749 2485855072663798129004953)
            ·
              refine ⟨1864391304497848596753715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2485855072663798129004953 1864391304497848596753715)
              ·
                refine ⟨2796586956746772895130573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1864391304497848596753715 2796586956746772895130573)
                ·
                  refine ⟨1048720108780039835673965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2796586956746772895130573 1048720108780039835673965)
                  ·
                    refine ⟨393270040792514938377737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1048720108780039835673965 393270040792514938377737)
                    ·
                      rfl

theorem cell22_1148836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_1148836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148836 prefixEnd_1148836 := by exact prefixLift 1148836
  have htrace : WordTrace (prefixWord ++ tailWord_1148836) baseStart_1148836 baseEnd_1148836 := by
    simpa [prefixWord, tailWord_1148836, baseEnd_1148836] using wordTrace_append hprefix tailTrace_1148836
  have hstable : (prefixWord ++ tailWord_1148836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148836).length < 2 ^ (prefixWord ++ tailWord_1148836).sum := by decide
  have hdescent : baseEnd_1148836 < baseStart_1148836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148847 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 2, 5]
def baseStart_1148847 : Nat := 118140960795 + 1148847 * 2 ^ 59
def prefixEnd_1148847 : Nat := 4983230072969 + 3 ^ 40 * 1148847 * 2
def baseEnd_1148847 : Nat := 393273806317314576352703

theorem tailTrace_1148847 : CollatzResearch.WordTrace tailWord_1148847 prefixEnd_1148847 393273806317314576352703 := by
  unfold tailWord_1148847
  simp only [CollatzResearch.WordTrace]
  refine ⟨41901892468931001291836795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27934594979287334194557863 41901892468931001291836795)
  ·
    refine ⟨62852838703396501937755193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41901892468931001291836795 62852838703396501937755193)
    ·
      refine ⟨47139629027547376453316395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62852838703396501937755193 47139629027547376453316395)
      ·
        refine ⟨70709443541321064679974593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47139629027547376453316395 70709443541321064679974593)
        ·
          refine ⟨53032082655990798509980945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70709443541321064679974593 53032082655990798509980945)
          ·
            refine ⟨39774061991993098882485709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53032082655990798509980945 39774061991993098882485709)
            ·
              refine ⟨14915273246997412080932141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39774061991993098882485709 14915273246997412080932141)
              ·
                refine ⟨5593227467624029530349553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14915273246997412080932141 5593227467624029530349553)
                ·
                  refine ⟨4194920600718022147762165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5593227467624029530349553 4194920600718022147762165)
                  ·
                    refine ⟨393273806317314576352703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4194920600718022147762165 393273806317314576352703)
                    ·
                      rfl

theorem cell22_1148847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_1148847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148847 prefixEnd_1148847 := by exact prefixLift 1148847
  have htrace : WordTrace (prefixWord ++ tailWord_1148847) baseStart_1148847 baseEnd_1148847 := by
    simpa [prefixWord, tailWord_1148847, baseEnd_1148847] using wordTrace_append hprefix tailTrace_1148847
  have hstable : (prefixWord ++ tailWord_1148847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148847).length < 2 ^ (prefixWord ++ tailWord_1148847).sum := by decide
  have hdescent : baseEnd_1148847 < baseStart_1148847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148879 : List Nat := [1, 1, 2, 1, 1, 5, 1, 5, 1, 4]
def baseStart_1148879 : Nat := 118140960795 + 1148879 * 2 ^ 59
def prefixEnd_1148879 : Nat := 4983230072969 + 3 ^ 40 * 1148879 * 2
def baseEnd_1148879 : Nat := 393284760571277159552605

theorem tailTrace_1148879 : CollatzResearch.WordTrace tailWord_1148879 prefixEnd_1148879 393284760571277159552605 := by
  unfold tailWord_1148879
  simp only [CollatzResearch.WordTrace]
  refine ⟨41903059604815070757001691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27935373069876713838001127 41903059604815070757001691)
  ·
    refine ⟨62854589407222606135502537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41903059604815070757001691 62854589407222606135502537)
    ·
      refine ⟨47140942055416954601626903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62854589407222606135502537 47140942055416954601626903)
      ·
        refine ⟨70711413083125431902440355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47140942055416954601626903 70711413083125431902440355)
        ·
          refine ⟨106067119624688147853660533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70711413083125431902440355 106067119624688147853660533)
          ·
            refine ⟨9943792464814513861280675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106067119624688147853660533 9943792464814513861280675)
            ·
              refine ⟨14915688697221770791921013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9943792464814513861280675 14915688697221770791921013)
              ·
                refine ⟨1398345815364541011742595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14915688697221770791921013 1398345815364541011742595)
                ·
                  refine ⟨2097518723046811517613893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1398345815364541011742595 2097518723046811517613893)
                  ·
                    refine ⟨393284760571277159552605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2097518723046811517613893 393284760571277159552605)
                    ·
                      rfl

theorem cell22_1148879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 4].length) (baseStart_1148879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148879 prefixEnd_1148879 := by exact prefixLift 1148879
  have htrace : WordTrace (prefixWord ++ tailWord_1148879) baseStart_1148879 baseEnd_1148879 := by
    simpa [prefixWord, tailWord_1148879, baseEnd_1148879] using wordTrace_append hprefix tailTrace_1148879
  have hstable : (prefixWord ++ tailWord_1148879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148879).length < 2 ^ (prefixWord ++ tailWord_1148879).sum := by decide
  have hdescent : baseEnd_1148879 < baseStart_1148879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148907 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 3, 6]
def baseStart_1148907 : Nat := 118140960795 + 1148907 * 2 ^ 59
def prefixEnd_1148907 : Nat := 4983230072969 + 3 ^ 40 * 1148907 * 2
def baseEnd_1148907 : Nat := 393294345543494419852519

theorem tailTrace_1148907 : CollatzResearch.WordTrace tailWord_1148907 prefixEnd_1148907 393294345543494419852519 := by
  unfold tailWord_1148907
  simp only [CollatzResearch.WordTrace]
  refine ⟨41904080848713631539020975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27936053899142421026013983 41904080848713631539020975)
  ·
    refine ⟨62856121273070447308531463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41904080848713631539020975 62856121273070447308531463)
    ·
      refine ⟨94284181909605670962797195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62856121273070447308531463 94284181909605670962797195)
      ·
        refine ⟨141426272864408506444195793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94284181909605670962797195 141426272864408506444195793)
        ·
          refine ⟨106069704648306379833146845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141426272864408506444195793 106069704648306379833146845)
          ·
            refine ⟨39776139243114892437430067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106069704648306379833146845 39776139243114892437430067)
            ·
              refine ⟨59664208864672338656145101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39776139243114892437430067 59664208864672338656145101)
              ·
                refine ⟨22374078324252126996054413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59664208864672338656145101 22374078324252126996054413)
                ·
                  refine ⟨8390279371594547623520405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22374078324252126996054413 8390279371594547623520405)
                  ·
                    refine ⟨393294345543494419852519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8390279371594547623520405 393294345543494419852519)
                    ·
                      rfl

theorem cell22_1148907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 6].length) (baseStart_1148907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148907 prefixEnd_1148907 := by exact prefixLift 1148907
  have htrace : WordTrace (prefixWord ++ tailWord_1148907) baseStart_1148907 baseEnd_1148907 := by
    simpa [prefixWord, tailWord_1148907, baseEnd_1148907] using wordTrace_append hprefix tailTrace_1148907
  have hstable : (prefixWord ++ tailWord_1148907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148907).length < 2 ^ (prefixWord ++ tailWord_1148907).sum := by decide
  have hdescent : baseEnd_1148907 < baseStart_1148907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148913 : List Nat := [1, 2, 2, 2, 5, 2, 1, 2, 1, 4]
def baseStart_1148913 : Nat := 118140960795 + 1148913 * 2 ^ 59
def prefixEnd_1148913 : Nat := 4983230072969 + 3 ^ 40 * 1148913 * 2
def baseEnd_1148913 : Nat := 393296399466112404202501

theorem tailTrace_1148913 : CollatzResearch.WordTrace tailWord_1148913 prefixEnd_1148913 393296399466112404202501 := by
  unfold tailWord_1148913
  simp only [CollatzResearch.WordTrace]
  refine ⟨41904299686691894563739393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27936199791127929709159595 41904299686691894563739393)
  ·
    refine ⟨31428224765018920922804545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41904299686691894563739393 31428224765018920922804545)
    ·
      refine ⟨23571168573764190692103409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31428224765018920922804545 23571168573764190692103409)
      ·
        refine ⟨17678376430323143019077557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23571168573764190692103409 17678376430323143019077557)
        ·
          refine ⟨1657347790342794658038521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17678376430323143019077557 1657347790342794658038521)
          ·
            refine ⟨1243010842757095993528891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1657347790342794658038521 1243010842757095993528891)
            ·
              refine ⟨1864516264135643990293337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243010842757095993528891 1864516264135643990293337)
              ·
                refine ⟨1398387198101732992720003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1864516264135643990293337 1398387198101732992720003)
                ·
                  refine ⟨2097580797152599489080005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1398387198101732992720003 2097580797152599489080005)
                  ·
                    refine ⟨393296399466112404202501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2097580797152599489080005 393296399466112404202501)
                    ·
                      rfl

theorem cell22_1148913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_1148913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148913 prefixEnd_1148913 := by exact prefixLift 1148913
  have htrace : WordTrace (prefixWord ++ tailWord_1148913) baseStart_1148913 baseEnd_1148913 := by
    simpa [prefixWord, tailWord_1148913, baseEnd_1148913] using wordTrace_append hprefix tailTrace_1148913
  have hstable : (prefixWord ++ tailWord_1148913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148913).length < 2 ^ (prefixWord ++ tailWord_1148913).sum := by decide
  have hdescent : baseEnd_1148913 < baseStart_1148913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148926 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_1148926 : Nat := 118140960795 + 1148926 * 2 ^ 59
def prefixEnd_1148926 : Nat := 4983230072969 + 3 ^ 40 * 1148926 * 2
def baseEnd_1148926 : Nat := 393300849631784703627461

theorem tailTrace_1148926 : CollatzResearch.WordTrace tailWord_1148926 prefixEnd_1148926 393300849631784703627461 := by
  unfold tailWord_1148926
  simp only [CollatzResearch.WordTrace]
  refine ⟨5238096729455599722995329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27936515890429865189308421 5238096729455599722995329)
  ·
    refine ⟨3928572547091699792246497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5238096729455599722995329 3928572547091699792246497)
    ·
      refine ⟨2946429410318774844184873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3928572547091699792246497 2946429410318774844184873)
      ·
        refine ⟨2209822057739081133138655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2946429410318774844184873 2209822057739081133138655)
        ·
          refine ⟨3314733086608621699707983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2209822057739081133138655 3314733086608621699707983)
          ·
            refine ⟨4972099629912932549561975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3314733086608621699707983 4972099629912932549561975)
            ·
              refine ⟨7458149444869398824342963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4972099629912932549561975 7458149444869398824342963)
              ·
                refine ⟨11187224167304098236514445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7458149444869398824342963 11187224167304098236514445)
                ·
                  refine ⟨4195209062739036838692917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11187224167304098236514445 4195209062739036838692917)
                  ·
                    refine ⟨393300849631784703627461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4195209062739036838692917 393300849631784703627461)
                    ·
                      rfl

theorem cell22_1148926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_1148926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148926 prefixEnd_1148926 := by exact prefixLift 1148926
  have htrace : WordTrace (prefixWord ++ tailWord_1148926) baseStart_1148926 baseEnd_1148926 := by
    simpa [prefixWord, tailWord_1148926, baseEnd_1148926] using wordTrace_append hprefix tailTrace_1148926
  have hstable : (prefixWord ++ tailWord_1148926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148926).length < 2 ^ (prefixWord ++ tailWord_1148926).sum := by decide
  have hdescent : baseEnd_1148926 < baseStart_1148926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148956 : List Nat := [2, 2, 3, 1, 3, 3, 1, 7]
def baseStart_1148956 : Nat := 118140960795 + 1148956 * 2 ^ 59
def prefixEnd_1148956 : Nat := 4983230072969 + 3 ^ 40 * 1148956 * 2
def baseEnd_1148956 : Nat := 43701235471652736153041

theorem tailTrace_1148956 : CollatzResearch.WordTrace tailWord_1148956 prefixEnd_1148956 43701235471652736153041 := by
  unfold tailWord_1148956
  simp only [CollatzResearch.WordTrace]
  refine ⟨20952934012768056453777361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27937245350357408605036481 20952934012768056453777361)
  ·
    refine ⟨15714700509576042340333021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20952934012768056453777361 15714700509576042340333021)
    ·
      refine ⟨5893012691091015877624883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15714700509576042340333021 5893012691091015877624883)
      ·
        refine ⟨8839519036636523816437325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5893012691091015877624883 8839519036636523816437325)
        ·
          refine ⟨3314819638738696431163997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8839519036636523816437325 3314819638738696431163997)
          ·
            refine ⟨1243057364527011161686499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3314819638738696431163997 1243057364527011161686499)
            ·
              refine ⟨1864586046790516742529749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243057364527011161686499 1864586046790516742529749)
              ·
                refine ⟨43701235471652736153041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1864586046790516742529749 43701235471652736153041)
                ·
                  rfl

theorem cell22_1148956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 7].length) (baseStart_1148956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148956 prefixEnd_1148956 := by exact prefixLift 1148956
  have htrace : WordTrace (prefixWord ++ tailWord_1148956) baseStart_1148956 baseEnd_1148956 := by
    simpa [prefixWord, tailWord_1148956, baseEnd_1148956] using wordTrace_append hprefix tailTrace_1148956
  have hstable : (prefixWord ++ tailWord_1148956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148956).length < 2 ^ (prefixWord ++ tailWord_1148956).sum := by decide
  have hdescent : baseEnd_1148956 < baseStart_1148956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148999 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 4, 5]
def baseStart_1148999 : Nat := 118140960795 + 1148999 * 2 ^ 59
def prefixEnd_1148999 : Nat := 4983230072969 + 3 ^ 40 * 1148999 * 2
def baseEnd_1148999 : Nat := 393325839023636846552237

theorem tailTrace_1148999 : CollatzResearch.WordTrace tailWord_1148999 prefixEnd_1148999 393325839023636846552237 := by
  unfold tailWord_1148999
  simp only [CollatzResearch.WordTrace]
  refine ⟨41907436364380331251370051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27938290909586887500913367 41907436364380331251370051)
  ·
    refine ⟨62861154546570496877055077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41907436364380331251370051 62861154546570496877055077)
    ·
      refine ⟨11786466477481968164447827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62861154546570496877055077 11786466477481968164447827)
      ·
        refine ⟨17679699716222952246671741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11786466477481968164447827 17679699716222952246671741)
        ·
          refine ⟨6629887393583607092501903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17679699716222952246671741 6629887393583607092501903)
          ·
            refine ⟨9944831090375410638752855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6629887393583607092501903 9944831090375410638752855)
            ·
              refine ⟨14917246635563115958129283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9944831090375410638752855 14917246635563115958129283)
              ·
                refine ⟨22375869953344673937193925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14917246635563115958129283 22375869953344673937193925)
                ·
                  refine ⟨4195475616252126363223861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22375869953344673937193925 4195475616252126363223861)
                  ·
                    refine ⟨393325839023636846552237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4195475616252126363223861 393325839023636846552237)
                    ·
                      rfl

theorem cell22_1148999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_1148999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1148999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1148999 prefixEnd_1148999 := by exact prefixLift 1148999
  have htrace : WordTrace (prefixWord ++ tailWord_1148999) baseStart_1148999 baseEnd_1148999 := by
    simpa [prefixWord, tailWord_1148999, baseEnd_1148999] using wordTrace_append hprefix tailTrace_1148999
  have hstable : (prefixWord ++ tailWord_1148999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148999).length < 2 ^ (prefixWord ++ tailWord_1148999).sum := by decide
  have hdescent : baseEnd_1148999 < baseStart_1148999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149005 : List Nat := [1, 6, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_1149005 : Nat := 118140960795 + 1149005 * 2 ^ 59
def prefixEnd_1149005 : Nat := 4983230072969 + 3 ^ 40 * 1149005 * 2
def baseEnd_1149005 : Nat := 393327892946254830902219

theorem tailTrace_1149005 : CollatzResearch.WordTrace tailWord_1149005 prefixEnd_1149005 393327892946254830902219 := by
  unfold tailWord_1149005
  simp only [CollatzResearch.WordTrace]
  refine ⟨41907655202358594276088469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27938436801572396184058979 41907655202358594276088469)
  ·
    refine ⟨1964421337610559106691647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41907655202358594276088469 1964421337610559106691647)
    ·
      refine ⟨2946632006415838660037471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1964421337610559106691647 2946632006415838660037471)
      ·
        refine ⟨4419948009623757990056207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2946632006415838660037471 4419948009623757990056207)
        ·
          refine ⟨6629922014435636985084311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4419948009623757990056207 6629922014435636985084311)
          ·
            refine ⟨9944883021653455477626467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6629922014435636985084311 9944883021653455477626467)
            ·
              refine ⟨14917324532480183216439701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9944883021653455477626467 14917324532480183216439701)
              ·
                refine ⟨699249587460008588270611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14917324532480183216439701 699249587460008588270611)
                ·
                  refine ⟨1048874381190012882405917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 699249587460008588270611 1048874381190012882405917)
                  ·
                    refine ⟨393327892946254830902219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1048874381190012882405917 393327892946254830902219)
                    ·
                      rfl

theorem cell22_1149005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_1149005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149005 prefixEnd_1149005 := by exact prefixLift 1149005
  have htrace : WordTrace (prefixWord ++ tailWord_1149005) baseStart_1149005 baseEnd_1149005 := by
    simpa [prefixWord, tailWord_1149005, baseEnd_1149005] using wordTrace_append hprefix tailTrace_1149005
  have hstable : (prefixWord ++ tailWord_1149005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149005).length < 2 ^ (prefixWord ++ tailWord_1149005).sum := by decide
  have hdescent : baseEnd_1149005 < baseStart_1149005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149082 : List Nat := [3, 1, 1, 5, 3, 1, 1, 2, 1, 4]
def baseStart_1149082 : Nat := 118140960795 + 1149082 * 2 ^ 59
def prefixEnd_1149082 : Nat := 4983230072969 + 3 ^ 40 * 1149082 * 2
def baseEnd_1149082 : Nat := 393354251619852296726983

theorem tailTrace_1149082 : CollatzResearch.WordTrace tailWord_1149082 prefixEnd_1149082 393354251619852296726983 := by
  unfold tailWord_1149082
  simp only [CollatzResearch.WordTrace]
  refine ⟨10477615905769909106660375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27940309082053090951094333 10477615905769909106660375)
  ·
    refine ⟨15716423858654863659990563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10477615905769909106660375 15716423858654863659990563)
    ·
      refine ⟨23574635787982295489985845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15716423858654863659990563 23574635787982295489985845)
      ·
        refine ⟨2210122105123340202186173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23574635787982295489985845 2210122105123340202186173)
        ·
          refine ⟨828795789421252575819815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2210122105123340202186173 828795789421252575819815)
          ·
            refine ⟨1243193684131878863729723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828795789421252575819815 1243193684131878863729723)
            ·
              refine ⟨1864790526197818295594585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243193684131878863729723 1864790526197818295594585)
              ·
                refine ⟨1398592894648363721695939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1864790526197818295594585 1398592894648363721695939)
                ·
                  refine ⟨2097889341972545582543909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1398592894648363721695939 2097889341972545582543909)
                  ·
                    refine ⟨393354251619852296726983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2097889341972545582543909 393354251619852296726983)
                    ·
                      rfl

theorem cell22_1149082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 1, 4].length) (baseStart_1149082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149082 prefixEnd_1149082 := by exact prefixLift 1149082
  have htrace : WordTrace (prefixWord ++ tailWord_1149082) baseStart_1149082 baseEnd_1149082 := by
    simpa [prefixWord, tailWord_1149082, baseEnd_1149082] using wordTrace_append hprefix tailTrace_1149082
  have hstable : (prefixWord ++ tailWord_1149082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149082).length < 2 ^ (prefixWord ++ tailWord_1149082).sum := by decide
  have hdescent : baseEnd_1149082 < baseStart_1149082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149104 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 3, 8]
def baseStart_1149104 : Nat := 118140960795 + 1149104 * 2 ^ 59
def prefixEnd_1149104 : Nat := 4983230072969 + 3 ^ 40 * 1149104 * 2
def baseEnd_1149104 : Nat := 393361782669451572676915

theorem tailTrace_1149104 : CollatzResearch.WordTrace tailWord_1149104 prefixEnd_1149104 393361782669451572676915 := by
  unfold tailWord_1149104
  simp only [CollatzResearch.WordTrace]
  refine ⟨20955633014499967091971183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27940844019333289455961577 20955633014499967091971183)
  ·
    refine ⟨31433449521749950637956775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20955633014499967091971183 31433449521749950637956775)
    ·
      refine ⟨47150174282624925956935163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31433449521749950637956775 47150174282624925956935163)
      ·
        refine ⟨70725261423937388935402745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47150174282624925956935163 70725261423937388935402745)
        ·
          refine ⟨53043946067953041701552059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70725261423937388935402745 53043946067953041701552059)
          ·
            refine ⟨79565919101929562552328089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53043946067953041701552059 79565919101929562552328089)
            ·
              refine ⟨59674439326447171914246067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79565919101929562552328089 59674439326447171914246067)
              ·
                refine ⟨89511658989670757871369101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59674439326447171914246067 89511658989670757871369101)
                ·
                  refine ⟨33566872121126534201763413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89511658989670757871369101 33566872121126534201763413)
                  ·
                    refine ⟨393361782669451572676915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33566872121126534201763413 393361782669451572676915)
                    ·
                      rfl

theorem cell22_1149104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_1149104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149104 prefixEnd_1149104 := by exact prefixLift 1149104
  have htrace : WordTrace (prefixWord ++ tailWord_1149104) baseStart_1149104 baseEnd_1149104 := by
    simpa [prefixWord, tailWord_1149104, baseEnd_1149104] using wordTrace_append hprefix tailTrace_1149104
  have hstable : (prefixWord ++ tailWord_1149104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149104).length < 2 ^ (prefixWord ++ tailWord_1149104).sum := by decide
  have hdescent : baseEnd_1149104 < baseStart_1149104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149157 : List Nat := [1, 3, 1, 4, 2, 2, 2, 3, 1, 3]
def baseStart_1149157 : Nat := 118140960795 + 1149157 * 2 ^ 59
def prefixEnd_1149157 : Nat := 4983230072969 + 3 ^ 40 * 1149157 * 2
def baseEnd_1149157 : Nat := 393379925652577101101753

theorem tailTrace_1149157 : CollatzResearch.WordTrace tailWord_1149157 prefixEnd_1149157 393379925652577101101753 := by
  unfold tailWord_1149157
  simp only [CollatzResearch.WordTrace]
  refine ⟨41913199097807924235621725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27942132731871949490414483 41913199097807924235621725)
  ·
    refine ⟨15717449661677971588358147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41913199097807924235621725 15717449661677971588358147)
    ·
      refine ⟨23576174492516957382537221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15717449661677971588358147 23576174492516957382537221)
      ·
        refine ⟨4420532717346929509225729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23576174492516957382537221 4420532717346929509225729)
        ·
          refine ⟨3315399538010197131919297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4420532717346929509225729 3315399538010197131919297)
          ·
            refine ⟨2486549653507647848939473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3315399538010197131919297 2486549653507647848939473)
            ·
              refine ⟨1864912240130735886704605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2486549653507647848939473 1864912240130735886704605)
              ·
                refine ⟨699342090049025957514227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1864912240130735886704605 699342090049025957514227)
                ·
                  refine ⟨1049013135073538936271341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 699342090049025957514227 1049013135073538936271341)
                  ·
                    refine ⟨393379925652577101101753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1049013135073538936271341 393379925652577101101753)
                    ·
                      rfl

theorem cell22_1149157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 1, 3].length) (baseStart_1149157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149157 prefixEnd_1149157 := by exact prefixLift 1149157
  have htrace : WordTrace (prefixWord ++ tailWord_1149157) baseStart_1149157 baseEnd_1149157 := by
    simpa [prefixWord, tailWord_1149157, baseEnd_1149157] using wordTrace_append hprefix tailTrace_1149157
  have hstable : (prefixWord ++ tailWord_1149157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149157).length < 2 ^ (prefixWord ++ tailWord_1149157).sum := by decide
  have hdescent : baseEnd_1149157 < baseStart_1149157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149170 : List Nat := [3, 2, 1, 3, 2, 3, 1, 2, 5]
def baseStart_1149170 : Nat := 118140960795 + 1149170 * 2 ^ 59
def prefixEnd_1149170 : Nat := 4983230072969 + 3 ^ 40 * 1149170 * 2
def baseEnd_1149170 : Nat := 131128125272749800175571

theorem tailTrace_1149170 : CollatzResearch.WordTrace tailWord_1149170 prefixEnd_1149170 131128125272749800175571 := by
  unfold tailWord_1149170
  simp only [CollatzResearch.WordTrace]
  refine ⟨10478418311690206863961241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27942448831173884970563309 10478418311690206863961241)
  ·
    refine ⟨7858813733767655147970931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10478418311690206863961241 7858813733767655147970931)
    ·
      refine ⟨11788220600651482721956397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7858813733767655147970931 11788220600651482721956397)
      ·
        refine ⟨4420582725244306020733649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11788220600651482721956397 4420582725244306020733649)
        ·
          refine ⟨3315437043933229515550237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4420582725244306020733649 3315437043933229515550237)
          ·
            refine ⟨1243288891474961068331339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3315437043933229515550237 1243288891474961068331339)
            ·
              refine ⟨1864933337212441602497009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243288891474961068331339 1864933337212441602497009)
              ·
                refine ⟨1398700002909331201872757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1864933337212441602497009 1398700002909331201872757)
                ·
                  refine ⟨131128125272749800175571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1398700002909331201872757 131128125272749800175571)
                  ·
                    rfl

theorem cell22_1149170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_1149170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149170 prefixEnd_1149170 := by exact prefixLift 1149170
  have htrace : WordTrace (prefixWord ++ tailWord_1149170) baseStart_1149170 baseEnd_1149170 := by
    simpa [prefixWord, tailWord_1149170, baseEnd_1149170] using wordTrace_append hprefix tailTrace_1149170
  have hstable : (prefixWord ++ tailWord_1149170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149170).length < 2 ^ (prefixWord ++ tailWord_1149170).sum := by decide
  have hdescent : baseEnd_1149170 < baseStart_1149170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149211 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 1, 6]
def baseStart_1149211 : Nat := 118140960795 + 1149211 * 2 ^ 59
def prefixEnd_1149211 : Nat := 4983230072969 + 3 ^ 40 * 1149211 * 2
def baseEnd_1149211 : Nat := 393398410956138960251587

theorem tailTrace_1149211 : CollatzResearch.WordTrace tailWord_1149211 prefixEnd_1149211 393398410956138960251587 := by
  unfold tailWord_1149211
  simp only [CollatzResearch.WordTrace]
  refine ⟨41915168639612291458087487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27943445759741527638724991 41915168639612291458087487)
  ·
    refine ⟨62872752959418437187131231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41915168639612291458087487 62872752959418437187131231)
    ·
      refine ⟨94309129439127655780696847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62872752959418437187131231 94309129439127655780696847)
      ·
        refine ⟨141463694158691483671045271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94309129439127655780696847 141463694158691483671045271)
        ·
          refine ⟨212195541238037225506567907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141463694158691483671045271 212195541238037225506567907)
          ·
            refine ⟨318293311857055838259851861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212195541238037225506567907 318293311857055838259851861)
            ·
              refine ⟨3729999748324873104607639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 318293311857055838259851861 3729999748324873104607639)
              ·
                refine ⟨5594999622487309656911459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3729999748324873104607639 5594999622487309656911459)
                ·
                  refine ⟨8392499433730964485367189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5594999622487309656911459 8392499433730964485367189)
                  ·
                    refine ⟨393398410956138960251587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8392499433730964485367189 393398410956138960251587)
                    ·
                      rfl

theorem cell22_1149211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 6].length) (baseStart_1149211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149211 prefixEnd_1149211 := by exact prefixLift 1149211
  have htrace : WordTrace (prefixWord ++ tailWord_1149211) baseStart_1149211 baseEnd_1149211 := by
    simpa [prefixWord, tailWord_1149211, baseEnd_1149211] using wordTrace_append hprefix tailTrace_1149211
  have hstable : (prefixWord ++ tailWord_1149211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149211).length < 2 ^ (prefixWord ++ tailWord_1149211).sum := by decide
  have hdescent : baseEnd_1149211 < baseStart_1149211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149215 : List Nat := [1, 1, 2, 4, 3, 1, 3, 3, 4]
def baseStart_1149215 : Nat := 118140960795 + 1149215 * 2 ^ 59
def prefixEnd_1149215 : Nat := 4983230072969 + 3 ^ 40 * 1149215 * 2
def baseEnd_1149215 : Nat := 131133260079294761050525

theorem tailTrace_1149215 : CollatzResearch.WordTrace tailWord_1149215 prefixEnd_1149215 131133260079294761050525 := by
  unfold tailWord_1149215
  simp only [CollatzResearch.WordTrace]
  refine ⟨41915314531597800141233099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27943543021065200094155399 41915314531597800141233099)
  ·
    refine ⟨62872971797396700211849649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41915314531597800141233099 62872971797396700211849649)
    ·
      refine ⟨47154728848047525158887237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62872971797396700211849649 47154728848047525158887237)
      ·
        refine ⟨8841511659008910967291357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47154728848047525158887237 8841511659008910967291357)
        ·
          refine ⟨3315566872128341612734259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8841511659008910967291357 3315566872128341612734259)
          ·
            refine ⟨4973350308192512419101389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3315566872128341612734259 4973350308192512419101389)
            ·
              refine ⟨1865006365572192157163021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4973350308192512419101389 1865006365572192157163021)
              ·
                refine ⟨699377387089572058936133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1865006365572192157163021 699377387089572058936133)
                ·
                  refine ⟨131133260079294761050525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 699377387089572058936133 131133260079294761050525)
                  ·
                    rfl

theorem cell22_1149215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 4].length) (baseStart_1149215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149215 prefixEnd_1149215 := by exact prefixLift 1149215
  have htrace : WordTrace (prefixWord ++ tailWord_1149215) baseStart_1149215 baseEnd_1149215 := by
    simpa [prefixWord, tailWord_1149215, baseEnd_1149215] using wordTrace_append hprefix tailTrace_1149215
  have hstable : (prefixWord ++ tailWord_1149215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149215).length < 2 ^ (prefixWord ++ tailWord_1149215).sum := by decide
  have hdescent : baseEnd_1149215 < baseStart_1149215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149348 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_1149348 : Nat := 118140960795 + 1149348 * 2 ^ 59
def prefixEnd_1149348 : Nat := 4983230072969 + 3 ^ 40 * 1149348 * 2
def baseEnd_1149348 : Nat := 393445308855916269576167

theorem tailTrace_1149348 : CollatzResearch.WordTrace tailWord_1149348 prefixEnd_1149348 393445308855916269576167 := by
  unfold tailWord_1149348
  simp only [CollatzResearch.WordTrace]
  refine ⟨20960082720057981927912349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27946776960077309237216465 20960082720057981927912349)
  ·
    refine ⟨7860031020021743222967131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20960082720057981927912349 7860031020021743222967131)
    ·
      refine ⟨11790046530032614834450697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7860031020021743222967131 11790046530032614834450697)
      ·
        refine ⟨8842534897524461125838023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11790046530032614834450697 8842534897524461125838023)
        ·
          refine ⟨13263802346286691688757035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8842534897524461125838023 13263802346286691688757035)
          ·
            refine ⟨19895703519430037533135553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13263802346286691688757035 19895703519430037533135553)
            ·
              refine ⟨14921777639572528149851665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19895703519430037533135553 14921777639572528149851665)
              ·
                refine ⟨11191333229679396112388749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14921777639572528149851665 11191333229679396112388749)
                ·
                  refine ⟨4196749961129773542145781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11191333229679396112388749 4196749961129773542145781)
                  ·
                    refine ⟨393445308855916269576167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4196749961129773542145781 393445308855916269576167)
                    ·
                      rfl

theorem cell22_1149348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_1149348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149348 prefixEnd_1149348 := by exact prefixLift 1149348
  have htrace : WordTrace (prefixWord ++ tailWord_1149348) baseStart_1149348 baseEnd_1149348 := by
    simpa [prefixWord, tailWord_1149348, baseEnd_1149348] using wordTrace_append hprefix tailTrace_1149348
  have hstable : (prefixWord ++ tailWord_1149348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149348).length < 2 ^ (prefixWord ++ tailWord_1149348).sum := by decide
  have hdescent : baseEnd_1149348 < baseStart_1149348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149408 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 2, 6]
def baseStart_1149408 : Nat := 118140960795 + 1149408 * 2 ^ 59
def prefixEnd_1149408 : Nat := 4983230072969 + 3 ^ 40 * 1149408 * 2
def baseEnd_1149408 : Nat := 393465848082096113075983

theorem tailTrace_1149408 : CollatzResearch.WordTrace tailWord_1149408 prefixEnd_1149408 393465848082096113075983 := by
  unfold tailWord_1149408
  simp only [CollatzResearch.WordTrace]
  refine ⟨20961176909949297051504439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27948235879932396068672585 20961176909949297051504439)
  ·
    refine ⟨31441765364923945577256659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20961176909949297051504439 31441765364923945577256659)
    ·
      refine ⟨47162648047385918365884989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31441765364923945577256659 47162648047385918365884989)
      ·
        refine ⟨17685993017769719387206871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47162648047385918365884989 17685993017769719387206871)
        ·
          refine ⟨26528989526654579080810307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17685993017769719387206871 26528989526654579080810307)
          ·
            refine ⟨39793484289981868621215461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26528989526654579080810307 39793484289981868621215461)
            ·
              refine ⟨7461278304371600366477899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39793484289981868621215461 7461278304371600366477899)
              ·
                refine ⟨11191917456557400549716849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7461278304371600366477899 11191917456557400549716849)
                ·
                  refine ⟨8393938092418050412287637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11191917456557400549716849 8393938092418050412287637)
                  ·
                    refine ⟨393465848082096113075983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8393938092418050412287637 393465848082096113075983)
                    ·
                      rfl

theorem cell22_1149408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_1149408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149408 prefixEnd_1149408 := by exact prefixLift 1149408
  have htrace : WordTrace (prefixWord ++ tailWord_1149408) baseStart_1149408 baseEnd_1149408 := by
    simpa [prefixWord, tailWord_1149408, baseEnd_1149408] using wordTrace_append hprefix tailTrace_1149408
  have hstable : (prefixWord ++ tailWord_1149408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149408).length < 2 ^ (prefixWord ++ tailWord_1149408).sum := by decide
  have hdescent : baseEnd_1149408 < baseStart_1149408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149472 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 2, 5]
def baseStart_1149472 : Nat := 118140960795 + 1149472 * 2 ^ 59
def prefixEnd_1149472 : Nat := 4983230072969 + 3 ^ 40 * 1149472 * 2
def baseEnd_1149472 : Nat := 393487756590021279475787

theorem tailTrace_1149472 : CollatzResearch.WordTrace tailWord_1149472 prefixEnd_1149472 393487756590021279475787 := by
  unfold tailWord_1149472
  simp only [CollatzResearch.WordTrace]
  refine ⟨20962344045833366516669335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27949792061111155355559113 20962344045833366516669335)
  ·
    refine ⟨31443516068750049775004003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20962344045833366516669335 31443516068750049775004003)
    ·
      refine ⟨47165274103125074662506005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31443516068750049775004003 47165274103125074662506005)
      ·
        refine ⟨2210872223583987874804969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47165274103125074662506005 2210872223583987874804969)
        ·
          refine ⟨1658154167687990906103727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2210872223583987874804969 1658154167687990906103727)
          ·
            refine ⟨2487231251531986359155591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1658154167687990906103727 2487231251531986359155591)
            ·
              refine ⟨3730846877297979538733387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2487231251531986359155591 3730846877297979538733387)
              ·
                refine ⟨5596270315946969308100081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3730846877297979538733387 5596270315946969308100081)
                ·
                  refine ⟨4197202736960226981075061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5596270315946969308100081 4197202736960226981075061)
                  ·
                    refine ⟨393487756590021279475787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4197202736960226981075061 393487756590021279475787)
                    ·
                      rfl

theorem cell22_1149472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 2, 5].length) (baseStart_1149472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149472 prefixEnd_1149472 := by exact prefixLift 1149472
  have htrace : WordTrace (prefixWord ++ tailWord_1149472) baseStart_1149472 baseEnd_1149472 := by
    simpa [prefixWord, tailWord_1149472, baseEnd_1149472] using wordTrace_append hprefix tailTrace_1149472
  have hstable : (prefixWord ++ tailWord_1149472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149472).length < 2 ^ (prefixWord ++ tailWord_1149472).sum := by decide
  have hdescent : baseEnd_1149472 < baseStart_1149472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149508 : List Nat := [2, 3, 5, 1, 1, 2, 1, 2, 5]
def baseStart_1149508 : Nat := 118140960795 + 1149508 * 2 ^ 59
def prefixEnd_1149508 : Nat := 4983230072969 + 3 ^ 40 * 1149508 * 2
def baseEnd_1149508 : Nat := 131166693375243061858559

theorem tailTrace_1149508 : CollatzResearch.WordTrace tailWord_1149508 prefixEnd_1149508 131166693375243061858559 := by
  unfold tailWord_1149508
  simp only [CollatzResearch.WordTrace]
  refine ⟨20963000559768155590824589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27950667413024207454432785 20963000559768155590824589)
  ·
    refine ⟨7861125209913058346559221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20963000559768155590824589 7861125209913058346559221)
    ·
      refine ⟨736980488429349219989927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7861125209913058346559221 736980488429349219989927)
      ·
        refine ⟨1105470732644023829984891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736980488429349219989927 1105470732644023829984891)
        ·
          refine ⟨1658206098966035744977337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1105470732644023829984891 1658206098966035744977337)
          ·
            refine ⟨1243654574224526808733003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1658206098966035744977337 1243654574224526808733003)
            ·
              refine ⟨1865481861336790213099505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243654574224526808733003 1865481861336790213099505)
              ·
                refine ⟨1399111396002592659824629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1865481861336790213099505 1399111396002592659824629)
                ·
                  refine ⟨131166693375243061858559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1399111396002592659824629 131166693375243061858559)
                  ·
                    rfl

theorem cell22_1149508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_1149508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149508 prefixEnd_1149508 := by exact prefixLift 1149508
  have htrace : WordTrace (prefixWord ++ tailWord_1149508) baseStart_1149508 baseEnd_1149508 := by
    simpa [prefixWord, tailWord_1149508, baseEnd_1149508] using wordTrace_append hprefix tailTrace_1149508
  have hstable : (prefixWord ++ tailWord_1149508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149508).length < 2 ^ (prefixWord ++ tailWord_1149508).sum := by decide
  have hdescent : baseEnd_1149508 < baseStart_1149508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149515 : List Nat := [1, 1, 1, 1, 3, 1, 4, 4, 2, 4]
def baseStart_1149515 : Nat := 118140960795 + 1149515 * 2 ^ 59
def prefixEnd_1149515 : Nat := 4983230072969 + 3 ^ 40 * 1149515 * 2
def baseEnd_1149515 : Nat := 393502476368783500650655

theorem tailTrace_1149515 : CollatzResearch.WordTrace tailWord_1149515 prefixEnd_1149515 393502476368783500650655 := by
  unfold tailWord_1149515
  simp only [CollatzResearch.WordTrace]
  refine ⟨41926256430510951377153999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27950837620340634251435999 41926256430510951377153999)
  ·
    refine ⟨62889384645766427065730999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41926256430510951377153999 62889384645766427065730999)
    ·
      refine ⟨94334076968649640598596499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62889384645766427065730999 94334076968649640598596499)
      ·
        refine ⟨141501115452974460897894749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94334076968649640598596499 141501115452974460897894749)
        ·
          refine ⟨53062918294865422836710531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141501115452974460897894749 53062918294865422836710531)
          ·
            refine ⟨79594377442298134255065797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53062918294865422836710531 79594377442298134255065797)
            ·
              refine ⟨14923945770430900172824837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79594377442298134255065797 14923945770430900172824837)
              ·
                refine ⟨2798239831955793782404657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14923945770430900172824837 2798239831955793782404657)
                ·
                  refine ⟨2098679873966845336803493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2798239831955793782404657 2098679873966845336803493)
                  ·
                    refine ⟨393502476368783500650655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2098679873966845336803493 393502476368783500650655)
                    ·
                      rfl

theorem cell22_1149515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 4].length) (baseStart_1149515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149515 prefixEnd_1149515 := by exact prefixLift 1149515
  have htrace : WordTrace (prefixWord ++ tailWord_1149515) baseStart_1149515 baseEnd_1149515 := by
    simpa [prefixWord, tailWord_1149515, baseEnd_1149515] using wordTrace_append hprefix tailTrace_1149515
  have hstable : (prefixWord ++ tailWord_1149515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149515).length < 2 ^ (prefixWord ++ tailWord_1149515).sum := by decide
  have hdescent : baseEnd_1149515 < baseStart_1149515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149570 : List Nat := [3, 4, 3, 1, 2, 1, 1, 1, 6]
def baseStart_1149570 : Nat := 118140960795 + 1149570 * 2 ^ 59
def prefixEnd_1149570 : Nat := 4983230072969 + 3 ^ 40 * 1149570 * 2
def baseEnd_1149570 : Nat := 131173767997593896841829

theorem tailTrace_1149570 : CollatzResearch.WordTrace tailWord_1149570 prefixEnd_1149570 131173767997593896841829 := by
  unfold tailWord_1149570
  simp only [CollatzResearch.WordTrace]
  refine ⟨10482065611327923942601541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27952174963541130513604109 10482065611327923942601541)
  ·
    refine ⟨1965387302123985739237789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10482065611327923942601541 1965387302123985739237789)
    ·
      refine ⟨737020238296494652214171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1965387302123985739237789 737020238296494652214171)
      ·
        refine ⟨1105530357444741978321257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 737020238296494652214171 1105530357444741978321257)
        ·
          refine ⟨829147768083556483740943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1105530357444741978321257 829147768083556483740943)
          ·
            refine ⟨1243721652125334725611415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829147768083556483740943 1243721652125334725611415)
            ·
              refine ⟨1865582478188002088417123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243721652125334725611415 1865582478188002088417123)
              ·
                refine ⟨2798373717282003132625685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1865582478188002088417123 2798373717282003132625685)
                ·
                  refine ⟨131173767997593896841829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2798373717282003132625685 131173767997593896841829)
                  ·
                    rfl

theorem cell22_1149570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_1149570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149570 prefixEnd_1149570 := by exact prefixLift 1149570
  have htrace : WordTrace (prefixWord ++ tailWord_1149570) baseStart_1149570 baseEnd_1149570 := by
    simpa [prefixWord, tailWord_1149570, baseEnd_1149570] using wordTrace_append hprefix tailTrace_1149570
  have hstable : (prefixWord ++ tailWord_1149570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149570).length < 2 ^ (prefixWord ++ tailWord_1149570).sum := by decide
  have hdescent : baseEnd_1149570 < baseStart_1149570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149575 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 7]
def baseStart_1149575 : Nat := 118140960795 + 1149575 * 2 ^ 59
def prefixEnd_1149575 : Nat := 4983230072969 + 3 ^ 40 * 1149575 * 2
def baseEnd_1149575 : Nat := 131174338531654448050157

theorem tailTrace_1149575 : CollatzResearch.WordTrace tailWord_1149575 prefixEnd_1149575 131174338531654448050157 := by
  unfold tailWord_1149575
  simp only [CollatzResearch.WordTrace]
  refine ⟨41928444810293581624338179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27952296540195721082892119 41928444810293581624338179)
  ·
    refine ⟨62892667215440372436507269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41928444810293581624338179 62892667215440372436507269)
    ·
      refine ⟨11792375102895069831845113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62892667215440372436507269 11792375102895069831845113)
      ·
        refine ⟨8844281327171302373883835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11792375102895069831845113 8844281327171302373883835)
        ·
          refine ⟨13266421990756953560825753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8844281327171302373883835 13266421990756953560825753)
          ·
            refine ⟨9949816493067715170619315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13266421990756953560825753 9949816493067715170619315)
            ·
              refine ⟨14924724739601572755928973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9949816493067715170619315 14924724739601572755928973)
              ·
                refine ⟨5596771777350589783473365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14924724739601572755928973 5596771777350589783473365)
                ·
                  refine ⟨131174338531654448050157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5596771777350589783473365 131174338531654448050157)
                  ·
                    rfl

theorem cell22_1149575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 7].length) (baseStart_1149575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149575 prefixEnd_1149575 := by exact prefixLift 1149575
  have htrace : WordTrace (prefixWord ++ tailWord_1149575) baseStart_1149575 baseEnd_1149575 := by
    simpa [prefixWord, tailWord_1149575, baseEnd_1149575] using wordTrace_append hprefix tailTrace_1149575
  have hstable : (prefixWord ++ tailWord_1149575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149575).length < 2 ^ (prefixWord ++ tailWord_1149575).sum := by decide
  have hdescent : baseEnd_1149575 < baseStart_1149575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149592 : List Nat := [2, 1, 2, 4, 1, 1, 3, 3, 5]
def baseStart_1149592 : Nat := 118140960795 + 1149592 * 2 ^ 59
def prefixEnd_1149592 : Nat := 4983230072969 + 3 ^ 40 * 1149592 * 2
def baseEnd_1149592 : Nat := 131176278347460322158473

theorem tailTrace_1149592 : CollatzResearch.WordTrace tailWord_1149592 prefixEnd_1149592 131176278347460322158473 := by
  unfold tailWord_1149592
  simp only [CollatzResearch.WordTrace]
  refine ⟨20964532425615996763853515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27952709900821329018471353 20964532425615996763853515)
  ·
    refine ⟨31446798638423995145780273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20964532425615996763853515 31446798638423995145780273)
    ·
      refine ⟨23585098978817996359335205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31446798638423995145780273 23585098978817996359335205)
      ·
        refine ⟨4422206058528374317375351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23585098978817996359335205 4422206058528374317375351)
        ·
          refine ⟨6633309087792561476063027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4422206058528374317375351 6633309087792561476063027)
          ·
            refine ⟨9949963631688842214094541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6633309087792561476063027 9949963631688842214094541)
            ·
              refine ⟨3731236361883315830285453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9949963631688842214094541 3731236361883315830285453)
              ·
                refine ⟨1399213635706243436357045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3731236361883315830285453 1399213635706243436357045)
                ·
                  refine ⟨131176278347460322158473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1399213635706243436357045 131176278347460322158473)
                  ·
                    rfl

theorem cell22_1149592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 5].length) (baseStart_1149592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149592 prefixEnd_1149592 := by exact prefixLift 1149592
  have htrace : WordTrace (prefixWord ++ tailWord_1149592) baseStart_1149592 baseEnd_1149592 := by
    simpa [prefixWord, tailWord_1149592, baseEnd_1149592] using wordTrace_append hprefix tailTrace_1149592
  have hstable : (prefixWord ++ tailWord_1149592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149592).length < 2 ^ (prefixWord ++ tailWord_1149592).sum := by decide
  have hdescent : baseEnd_1149592 < baseStart_1149592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149682 : List Nat := [3, 2, 1, 3, 1, 3, 9]
def baseStart_1149682 : Nat := 118140960795 + 1149682 * 2 ^ 59
def prefixEnd_1149682 : Nat := 4983230072969 + 3 ^ 40 * 1149682 * 2
def baseEnd_1149682 : Nat := 14576283106727804878709

theorem tailTrace_1149682 : CollatzResearch.WordTrace tailWord_1149682 prefixEnd_1149682 14576283106727804878709 := by
  unfold tailWord_1149682
  simp only [CollatzResearch.WordTrace]
  refine ⟨10483086855226484724620825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27954898280603959265655533 10483086855226484724620825)
  ·
    refine ⟨7862315141419863543465619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10483086855226484724620825 7862315141419863543465619)
    ·
      refine ⟨11793472712129795315198429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7862315141419863543465619 11793472712129795315198429)
      ·
        refine ⟨4422552267048673243199411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11793472712129795315198429 4422552267048673243199411)
        ·
          refine ⟨6633828400573009864799117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4422552267048673243199411 6633828400573009864799117)
          ·
            refine ⟨2487685650214878699299669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6633828400573009864799117 2487685650214878699299669)
            ·
              refine ⟨14576283106727804878709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2487685650214878699299669 14576283106727804878709)
              ·
                rfl

theorem cell22_1149682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 9].length) (baseStart_1149682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149682 prefixEnd_1149682 := by exact prefixLift 1149682
  have htrace : WordTrace (prefixWord ++ tailWord_1149682) baseStart_1149682 baseEnd_1149682 := by
    simpa [prefixWord, tailWord_1149682, baseEnd_1149682] using wordTrace_append hprefix tailTrace_1149682
  have hstable : (prefixWord ++ tailWord_1149682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149682).length < 2 ^ (prefixWord ++ tailWord_1149682).sum := by decide
  have hdescent : baseEnd_1149682 < baseStart_1149682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149703 : List Nat := [1, 1, 4, 4, 1, 2, 3, 1, 2, 3]
def baseStart_1149703 : Nat := 118140960795 + 1149703 * 2 ^ 59
def prefixEnd_1149703 : Nat := 4983230072969 + 3 ^ 40 * 1149703 * 2
def baseEnd_1149703 : Nat := 393566832610813676950079

theorem tailTrace_1149703 : CollatzResearch.WordTrace tailWord_1149703 prefixEnd_1149703 393566832610813676950079 := by
  unfold tailWord_1149703
  simp only [CollatzResearch.WordTrace]
  refine ⟨41933113353829859484997763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27955408902553239656665175 41933113353829859484997763)
  ·
    refine ⟨62899670030744789227496645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41933113353829859484997763 62899670030744789227496645)
    ·
      refine ⟨11793688130764647980155621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62899670030744789227496645 11793688130764647980155621)
      ·
        refine ⟨2211316524518371496279179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11793688130764647980155621 2211316524518371496279179)
        ·
          refine ⟨3316974786777557244418769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2211316524518371496279179 3316974786777557244418769)
          ·
            refine ⟨2487731090083167933314077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3316974786777557244418769 2487731090083167933314077)
            ·
              refine ⟨932899158781187974992779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2487731090083167933314077 932899158781187974992779)
              ·
                refine ⟨1399348738171781962489169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 932899158781187974992779 1399348738171781962489169)
                ·
                  refine ⟨1049511553628836471866877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1399348738171781962489169 1049511553628836471866877)
                  ·
                    refine ⟨393566832610813676950079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1049511553628836471866877 393566832610813676950079)
                    ·
                      rfl

theorem cell22_1149703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_1149703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149703 prefixEnd_1149703 := by exact prefixLift 1149703
  have htrace : WordTrace (prefixWord ++ tailWord_1149703) baseStart_1149703 baseEnd_1149703 := by
    simpa [prefixWord, tailWord_1149703, baseEnd_1149703] using wordTrace_append hprefix tailTrace_1149703
  have hstable : (prefixWord ++ tailWord_1149703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149703).length < 2 ^ (prefixWord ++ tailWord_1149703).sum := by decide
  have hdescent : baseEnd_1149703 < baseStart_1149703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149727 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 7]
def baseStart_1149727 : Nat := 118140960795 + 1149727 * 2 ^ 59
def prefixEnd_1149727 : Nat := 4983230072969 + 3 ^ 40 * 1149727 * 2
def baseEnd_1149727 : Nat := 131191682767095204783335

theorem tailTrace_1149727 : CollatzResearch.WordTrace tailWord_1149727 prefixEnd_1149727 131191682767095204783335 := by
  unfold tailWord_1149727
  simp only [CollatzResearch.WordTrace]
  refine ⟨41933988705742911583871435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27955992470495274389247623 41933988705742911583871435)
  ·
    refine ⟨62900983058614367375807153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41933988705742911583871435 62900983058614367375807153)
    ·
      refine ⟨47175737293960775531855365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62900983058614367375807153 47175737293960775531855365)
      ·
        refine ⟨8845450742617645412222881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47175737293960775531855365 8845450742617645412222881)
        ·
          refine ⟨6634088056963234059167161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8845450742617645412222881 6634088056963234059167161)
          ·
            refine ⟨4975566042722425544375371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6634088056963234059167161 4975566042722425544375371)
            ·
              refine ⟨7463349064083638316563057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4975566042722425544375371 7463349064083638316563057)
              ·
                refine ⟨5597511798062728737422293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7463349064083638316563057 5597511798062728737422293)
                ·
                  refine ⟨131191682767095204783335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5597511798062728737422293 131191682767095204783335)
                  ·
                    rfl

theorem cell22_1149727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 7].length) (baseStart_1149727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149727 prefixEnd_1149727 := by exact prefixLift 1149727
  have htrace : WordTrace (prefixWord ++ tailWord_1149727) baseStart_1149727 baseEnd_1149727 := by
    simpa [prefixWord, tailWord_1149727, baseEnd_1149727] using wordTrace_append hprefix tailTrace_1149727
  have hstable : (prefixWord ++ tailWord_1149727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149727).length < 2 ^ (prefixWord ++ tailWord_1149727).sum := by decide
  have hdescent : baseEnd_1149727 < baseStart_1149727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149791 : List Nat := [1, 1, 2, 3, 1, 3, 5, 1, 1, 4]
def baseStart_1149791 : Nat := 118140960795 + 1149791 * 2 ^ 59
def prefixEnd_1149791 : Nat := 4983230072969 + 3 ^ 40 * 1149791 * 2
def baseEnd_1149791 : Nat := 393596956809210780749809

theorem tailTrace_1149791 : CollatzResearch.WordTrace tailWord_1149791 prefixEnd_1149791 393596956809210780749809 := by
  unfold tailWord_1149791
  simp only [CollatzResearch.WordTrace]
  refine ⟨41936322977511050514201227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27957548651674033676134151 41936322977511050514201227)
  ·
    refine ⟨62904484466266575771301841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41936322977511050514201227 62904484466266575771301841)
    ·
      refine ⟨47178363349699931828476381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62904484466266575771301841 47178363349699931828476381)
      ·
        refine ⟨17691886256137474435678643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47178363349699931828476381 17691886256137474435678643)
        ·
          refine ⟨26537829384206211653517965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17691886256137474435678643 26537829384206211653517965)
          ·
            refine ⟨9951686019077329370069237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26537829384206211653517965 9951686019077329370069237)
            ·
              refine ⟨932970564288499628443991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9951686019077329370069237 932970564288499628443991)
              ·
                refine ⟨1399455846432749442665987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 932970564288499628443991 1399455846432749442665987)
                ·
                  refine ⟨2099183769649124163998981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1399455846432749442665987 2099183769649124163998981)
                  ·
                    refine ⟨393596956809210780749809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2099183769649124163998981 393596956809210780749809)
                    ·
                      rfl

theorem cell22_1149791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 1, 4].length) (baseStart_1149791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149791 prefixEnd_1149791 := by exact prefixLift 1149791
  have htrace : WordTrace (prefixWord ++ tailWord_1149791) baseStart_1149791 baseEnd_1149791 := by
    simpa [prefixWord, tailWord_1149791, baseEnd_1149791] using wordTrace_append hprefix tailTrace_1149791
  have hstable : (prefixWord ++ tailWord_1149791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149791).length < 2 ^ (prefixWord ++ tailWord_1149791).sum := by decide
  have hdescent : baseEnd_1149791 < baseStart_1149791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149821 : List Nat := [1, 4, 1, 1, 2, 1, 4, 3, 2, 3]
def baseStart_1149821 : Nat := 118140960795 + 1149821 * 2 ^ 59
def prefixEnd_1149821 : Nat := 4983230072969 + 3 ^ 40 * 1149821 * 2
def baseEnd_1149821 : Nat := 393607226422300702499717

theorem tailTrace_1149821 : CollatzResearch.WordTrace tailWord_1149821 prefixEnd_1149821 393607226422300702499717 := by
  unfold tailWord_1149821
  simp only [CollatzResearch.WordTrace]
  refine ⟨41937417167402365637793317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27958278111601577091862211 41937417167402365637793317)
  ·
    refine ⟨7863265718887943557086247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41937417167402365637793317 7863265718887943557086247)
    ·
      refine ⟨11794898578331915335629371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7863265718887943557086247 11794898578331915335629371)
      ·
        refine ⟨17692347867497873003444057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11794898578331915335629371 17692347867497873003444057)
        ·
          refine ⟨13269260900623404752583043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17692347867497873003444057 13269260900623404752583043)
          ·
            refine ⟨19903891350935107128874565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13269260900623404752583043 19903891350935107128874565)
            ·
              refine ⟨3731979628300332586663981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19903891350935107128874565 3731979628300332586663981)
              ·
                refine ⟨1399492360612624719998993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3731979628300332586663981 1399492360612624719998993)
                ·
                  refine ⟨1049619270459468539999245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1399492360612624719998993 1049619270459468539999245)
                  ·
                    refine ⟨393607226422300702499717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1049619270459468539999245 393607226422300702499717)
                    ·
                      rfl

theorem cell22_1149821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_1149821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149821 prefixEnd_1149821 := by exact prefixLift 1149821
  have htrace : WordTrace (prefixWord ++ tailWord_1149821) baseStart_1149821 baseEnd_1149821 := by
    simpa [prefixWord, tailWord_1149821, baseEnd_1149821] using wordTrace_append hprefix tailTrace_1149821
  have hstable : (prefixWord ++ tailWord_1149821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149821).length < 2 ^ (prefixWord ++ tailWord_1149821).sum := by decide
  have hdescent : baseEnd_1149821 < baseStart_1149821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149842 : List Nat := [3, 2, 3, 2, 3, 1, 2, 1, 1, 4]
def baseStart_1149842 : Nat := 118140960795 + 1149842 * 2 ^ 59
def prefixEnd_1149842 : Nat := 4983230072969 + 3 ^ 40 * 1149842 * 2
def baseEnd_1149842 : Nat := 393614415151463647724653

theorem tailTrace_1149842 : CollatzResearch.WordTrace tailWord_1149842 prefixEnd_1149842 393614415151463647724653 := by
  unfold tailWord_1149842
  simp only [CollatzResearch.WordTrace]
  refine ⟨10484545775081571556076945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27958788733550857482871853 10484545775081571556076945)
  ·
    refine ⟨7863409331311178667057709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10484545775081571556076945 7863409331311178667057709)
    ·
      refine ⟨2948778499241692000146641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7863409331311178667057709 2948778499241692000146641)
      ·
        refine ⟨2211583874431269000109981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2948778499241692000146641 2211583874431269000109981)
        ·
          refine ⟨829343952911725875041243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2211583874431269000109981 829343952911725875041243)
          ·
            refine ⟨1244015929367588812561865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829343952911725875041243 1244015929367588812561865)
            ·
              refine ⟨933011947025691609421399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1244015929367588812561865 933011947025691609421399)
              ·
                refine ⟨1399517920538537414132099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 933011947025691609421399 1399517920538537414132099)
                ·
                  refine ⟨2099276880807806121198149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1399517920538537414132099 2099276880807806121198149)
                  ·
                    refine ⟨393614415151463647724653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2099276880807806121198149 393614415151463647724653)
                    ·
                      rfl

theorem cell22_1149842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_1149842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149842 prefixEnd_1149842 := by exact prefixLift 1149842
  have htrace : WordTrace (prefixWord ++ tailWord_1149842) baseStart_1149842 baseEnd_1149842 := by
    simpa [prefixWord, tailWord_1149842, baseEnd_1149842] using wordTrace_append hprefix tailTrace_1149842
  have hstable : (prefixWord ++ tailWord_1149842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149842).length < 2 ^ (prefixWord ++ tailWord_1149842).sum := by decide
  have hdescent : baseEnd_1149842 < baseStart_1149842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149849 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 7, 3]
def baseStart_1149849 : Nat := 118140960795 + 1149849 * 2 ^ 59
def prefixEnd_1149849 : Nat := 4983230072969 + 3 ^ 40 * 1149849 * 2
def baseEnd_1149849 : Nat := 393616811394517962799631

theorem tailTrace_1149849 : CollatzResearch.WordTrace tailWord_1149849 prefixEnd_1149849 393616811394517962799631 := by
  unfold tailWord_1149849
  simp only [CollatzResearch.WordTrace]
  refine ⟨41938438411300926419812601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27958958940867284279875067 41938438411300926419812601)
  ·
    refine ⟨31453828808475694814859451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41938438411300926419812601 31453828808475694814859451)
    ·
      refine ⟨47180743212713542222289177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31453828808475694814859451 47180743212713542222289177)
      ·
        refine ⟨35385557409535156666716883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47180743212713542222289177 35385557409535156666716883)
        ·
          refine ⟨53078336114302735000075325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35385557409535156666716883 53078336114302735000075325)
          ·
            refine ⟨19904376042863525625028247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53078336114302735000075325 19904376042863525625028247)
            ·
              refine ⟨29856564064295288437542371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19904376042863525625028247 29856564064295288437542371)
              ·
                refine ⟨44784846096442932656313557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29856564064295288437542371 44784846096442932656313557)
                ·
                  refine ⟨1049644830385381234132349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 44784846096442932656313557 1049644830385381234132349)
                  ·
                    refine ⟨393616811394517962799631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1049644830385381234132349 393616811394517962799631)
                    ·
                      rfl

theorem cell22_1149849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 3].length) (baseStart_1149849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149849 prefixEnd_1149849 := by exact prefixLift 1149849
  have htrace : WordTrace (prefixWord ++ tailWord_1149849) baseStart_1149849 baseEnd_1149849 := by
    simpa [prefixWord, tailWord_1149849, baseEnd_1149849] using wordTrace_append hprefix tailTrace_1149849
  have hstable : (prefixWord ++ tailWord_1149849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149849).length < 2 ^ (prefixWord ++ tailWord_1149849).sum := by decide
  have hdescent : baseEnd_1149849 < baseStart_1149849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149879 : List Nat := [1, 1, 3, 1, 3, 1, 2, 5, 5]
def baseStart_1149879 : Nat := 118140960795 + 1149879 * 2 ^ 59
def prefixEnd_1149879 : Nat := 4983230072969 + 3 ^ 40 * 1149879 * 2
def baseEnd_1149879 : Nat := 131209027002535961516513

theorem tailTrace_1149879 : CollatzResearch.WordTrace tailWord_1149879 prefixEnd_1149879 131209027002535961516513 := by
  unfold tailWord_1149879
  simp only [CollatzResearch.WordTrace]
  refine ⟨41939532601192241543404691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27959688400794827695603127 41939532601192241543404691)
  ·
    refine ⟨62909298901788362315107037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41939532601192241543404691 62909298901788362315107037)
    ·
      refine ⟨23590987088170635868165139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62909298901788362315107037 23590987088170635868165139)
      ·
        refine ⟨35386480632255953802247709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23590987088170635868165139 35386480632255953802247709)
        ·
          refine ⟨13269930237095982675842891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35386480632255953802247709 13269930237095982675842891)
          ·
            refine ⟨19904895355643974013764337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13269930237095982675842891 19904895355643974013764337)
            ·
              refine ⟨14928671516732980510323253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19904895355643974013764337 14928671516732980510323253)
              ·
                refine ⟨1399562954693716922842805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14928671516732980510323253 1399562954693716922842805)
                ·
                  refine ⟨131209027002535961516513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1399562954693716922842805 131209027002535961516513)
                  ·
                    rfl

theorem cell22_1149879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 5].length) (baseStart_1149879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149879 prefixEnd_1149879 := by exact prefixLift 1149879
  have htrace : WordTrace (prefixWord ++ tailWord_1149879) baseStart_1149879 baseEnd_1149879 := by
    simpa [prefixWord, tailWord_1149879, baseEnd_1149879] using wordTrace_append hprefix tailTrace_1149879
  have hstable : (prefixWord ++ tailWord_1149879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149879).length < 2 ^ (prefixWord ++ tailWord_1149879).sum := by decide
  have hdescent : baseEnd_1149879 < baseStart_1149879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149917 : List Nat := [1, 4, 3, 1, 2, 2, 3, 2, 1, 3]
def baseStart_1149917 : Nat := 118140960795 + 1149917 * 2 ^ 59
def prefixEnd_1149917 : Nat := 4983230072969 + 3 ^ 40 * 1149917 * 2
def baseEnd_1149917 : Nat := 393640089184188452099423

theorem tailTrace_1149917 : CollatzResearch.WordTrace tailWord_1149917 prefixEnd_1149917 393640089184188452099423 := by
  unfold tailWord_1149917
  simp only [CollatzResearch.WordTrace]
  refine ⟨41940918575054574033288005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27960612383369716022192003 41940918575054574033288005)
  ·
    refine ⟨7863922232822732631241501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41940918575054574033288005 7863922232822732631241501)
    ·
      refine ⟨2948970837308524736715563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7863922232822732631241501 2948970837308524736715563)
      ·
        refine ⟨4423456255962787105073345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2948970837308524736715563 4423456255962787105073345)
        ·
          refine ⟨3317592191972090328805009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4423456255962787105073345 3317592191972090328805009)
          ·
            refine ⟨2488194143979067746603757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3317592191972090328805009 2488194143979067746603757)
            ·
              refine ⟨933072803992150404976409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2488194143979067746603757 933072803992150404976409)
              ·
                refine ⟨699804602994112803732307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 933072803992150404976409 699804602994112803732307)
                ·
                  refine ⟨1049706904491169205598461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 699804602994112803732307 1049706904491169205598461)
                  ·
                    refine ⟨393640089184188452099423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1049706904491169205598461 393640089184188452099423)
                    ·
                      rfl

theorem cell22_1149917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_1149917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149917 prefixEnd_1149917 := by exact prefixLift 1149917
  have htrace : WordTrace (prefixWord ++ tailWord_1149917) baseStart_1149917 baseEnd_1149917 := by
    simpa [prefixWord, tailWord_1149917, baseEnd_1149917] using wordTrace_append hprefix tailTrace_1149917
  have hstable : (prefixWord ++ tailWord_1149917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149917).length < 2 ^ (prefixWord ++ tailWord_1149917).sum := by decide
  have hdescent : baseEnd_1149917 < baseStart_1149917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149924 : List Nat := [2, 3, 1, 1, 1, 1, 2, 5, 6]
def baseStart_1149924 : Nat := 118140960795 + 1149924 * 2 ^ 59
def prefixEnd_1149924 : Nat := 4983230072969 + 3 ^ 40 * 1149924 * 2
def baseEnd_1149924 : Nat := 131214161809080922391467

theorem tailTrace_1149924 : CollatzResearch.WordTrace tailWord_1149924 prefixEnd_1149924 131214161809080922391467 := by
  unfold tailWord_1149924
  simp only [CollatzResearch.WordTrace]
  refine ⟨20970586943014607114396413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27960782590686142819195217 20970586943014607114396413)
  ·
    refine ⟨7863970103630477667898655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20970586943014607114396413 7863970103630477667898655)
    ·
      refine ⟨11795955155445716501847983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7863970103630477667898655 11795955155445716501847983)
      ·
        refine ⟨17693932733168574752771975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11795955155445716501847983 17693932733168574752771975)
        ·
          refine ⟨26540899099752862129157963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17693932733168574752771975 26540899099752862129157963)
          ·
            refine ⟨39811348649629293193736945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26540899099752862129157963 39811348649629293193736945)
            ·
              refine ⟨29858511487221969895302709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39811348649629293193736945 29858511487221969895302709)
              ·
                refine ⟨2799235451927059677684629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29858511487221969895302709 2799235451927059677684629)
                ·
                  refine ⟨131214161809080922391467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2799235451927059677684629 131214161809080922391467)
                  ·
                    rfl

theorem cell22_1149924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_1149924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149924 prefixEnd_1149924 := by exact prefixLift 1149924
  have htrace : WordTrace (prefixWord ++ tailWord_1149924) baseStart_1149924 baseEnd_1149924 := by
    simpa [prefixWord, tailWord_1149924, baseEnd_1149924] using wordTrace_append hprefix tailTrace_1149924
  have hstable : (prefixWord ++ tailWord_1149924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149924).length < 2 ^ (prefixWord ++ tailWord_1149924).sum := by decide
  have hdescent : baseEnd_1149924 < baseStart_1149924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149973 : List Nat := [1, 3, 2, 1, 4, 1, 1, 4, 2, 3]
def baseStart_1149973 : Nat := 118140960795 + 1149973 * 2 ^ 59
def prefixEnd_1149973 : Nat := 4983230072969 + 3 ^ 40 * 1149973 * 2
def baseEnd_1149973 : Nat := 393659259128622972699251

theorem tailTrace_1149973 : CollatzResearch.WordTrace tailWord_1149973 prefixEnd_1149973 393659259128622972699251 := by
  unfold tailWord_1149973
  simp only [CollatzResearch.WordTrace]
  refine ⟨41942961062851695597326573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27961974041901130398217715 41942961062851695597326573)
  ·
    refine ⟨15728610398569385848997465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41942961062851695597326573 15728610398569385848997465)
    ·
      refine ⟨11796457798927039386748099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15728610398569385848997465 11796457798927039386748099)
      ·
        refine ⟨17694686698390559080122149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11796457798927039386748099 17694686698390559080122149)
        ·
          refine ⟨3317753755948229827522903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17694686698390559080122149 3317753755948229827522903)
          ·
            refine ⟨4976630633922344741284355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3317753755948229827522903 4976630633922344741284355)
            ·
              refine ⟨7464945950883517111926533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4976630633922344741284355 7464945950883517111926533)
              ·
                refine ⟨1399677365790659458486225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7464945950883517111926533 1399677365790659458486225)
                ·
                  refine ⟨1049758024342994593864669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1399677365790659458486225 1049758024342994593864669)
                  ·
                    refine ⟨393659259128622972699251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1049758024342994593864669 393659259128622972699251)
                    ·
                      rfl

theorem cell22_1149973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_1149973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149973 prefixEnd_1149973 := by exact prefixLift 1149973
  have htrace : WordTrace (prefixWord ++ tailWord_1149973) baseStart_1149973 baseEnd_1149973 := by
    simpa [prefixWord, tailWord_1149973, baseEnd_1149973] using wordTrace_append hprefix tailTrace_1149973
  have hstable : (prefixWord ++ tailWord_1149973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149973).length < 2 ^ (prefixWord ++ tailWord_1149973).sum := by decide
  have hdescent : baseEnd_1149973 < baseStart_1149973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149975 : List Nat := [1, 1, 3, 5, 1, 1, 4, 2, 4]
def baseStart_1149975 : Nat := 118140960795 + 1149975 * 2 ^ 59
def prefixEnd_1149975 : Nat := 4983230072969 + 3 ^ 40 * 1149975 * 2
def baseEnd_1149975 : Nat := 131219981256498544716415

theorem tailTrace_1149975 : CollatzResearch.WordTrace tailWord_1149975 prefixEnd_1149975 131219981256498544716415 := by
  unfold tailWord_1149975
  simp only [CollatzResearch.WordTrace]
  refine ⟨41943034008844449938899379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27962022672562966625932919 41943034008844449938899379)
  ·
    refine ⟨62914551013266674908349069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41943034008844449938899379 62914551013266674908349069)
    ·
      refine ⟨23592956629975003090630901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62914551013266674908349069 23592956629975003090630901)
      ·
        refine ⟨2211839684060156539746647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23592956629975003090630901 2211839684060156539746647)
        ·
          refine ⟨3317759526090234809619971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2211839684060156539746647 3317759526090234809619971)
          ·
            refine ⟨4976639289135352214429957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3317759526090234809619971 4976639289135352214429957)
            ·
              refine ⟨933119866712878540205617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4976639289135352214429957 933119866712878540205617)
              ·
                refine ⟨699839900034658905154213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 933119866712878540205617 699839900034658905154213)
                ·
                  refine ⟨131219981256498544716415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 699839900034658905154213 131219981256498544716415)
                  ·
                    rfl

theorem cell22_1149975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 4].length) (baseStart_1149975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149975 prefixEnd_1149975 := by exact prefixLift 1149975
  have htrace : WordTrace (prefixWord ++ tailWord_1149975) baseStart_1149975 baseEnd_1149975 := by
    simpa [prefixWord, tailWord_1149975, baseEnd_1149975] using wordTrace_append hprefix tailTrace_1149975
  have hstable : (prefixWord ++ tailWord_1149975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149975).length < 2 ^ (prefixWord ++ tailWord_1149975).sum := by decide
  have hdescent : baseEnd_1149975 < baseStart_1149975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149986 : List Nat := [3, 3, 1, 1, 1, 3, 3, 7]
def baseStart_1149986 : Nat := 118140960795 + 1149986 * 2 ^ 59
def prefixEnd_1149986 : Nat := 4983230072969 + 3 ^ 40 * 1149986 * 2
def baseEnd_1149986 : Nat := 43740412143810585791579

theorem tailTrace_1149986 : CollatzResearch.WordTrace tailWord_1149986 prefixEnd_1149986 43740412143810585791579 := by
  unfold tailWord_1149986
  simp only [CollatzResearch.WordTrace]
  refine ⟨10485858802951149704387453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27962290141203065878366541 10485858802951149704387453)
  ·
    refine ⟨3932197051106681139145295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10485858802951149704387453 3932197051106681139145295)
    ·
      refine ⟨5898295576660021708717943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3932197051106681139145295 5898295576660021708717943)
      ·
        refine ⟨8847443364990032563076915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5898295576660021708717943 8847443364990032563076915)
        ·
          refine ⟨13271165047485048844615373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8847443364990032563076915 13271165047485048844615373)
          ·
            refine ⟨4976686892806893316730765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13271165047485048844615373 4976686892806893316730765)
            ·
              refine ⟨1866257584802584993774037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4976686892806893316730765 1866257584802584993774037)
              ·
                refine ⟨43740412143810585791579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1866257584802584993774037 43740412143810585791579)
                ·
                  rfl

theorem cell22_1149986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 7].length) (baseStart_1149986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1149986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1149986 prefixEnd_1149986 := by exact prefixLift 1149986
  have htrace : WordTrace (prefixWord ++ tailWord_1149986) baseStart_1149986 baseEnd_1149986 := by
    simpa [prefixWord, tailWord_1149986, baseEnd_1149986] using wordTrace_append hprefix tailTrace_1149986
  have hstable : (prefixWord ++ tailWord_1149986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149986).length < 2 ^ (prefixWord ++ tailWord_1149986).sum := by decide
  have hdescent : baseEnd_1149986 < baseStart_1149986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150048 : List Nat := [2, 1, 1, 3, 2, 2, 5, 1, 5]
def baseStart_1150048 : Nat := 118140960795 + 1150048 * 2 ^ 59
def prefixEnd_1150048 : Nat := 4983230072969 + 3 ^ 40 * 1150048 * 2
def baseEnd_1150048 : Nat := 131228311053782592358007

theorem tailTrace_1150048 : CollatzResearch.WordTrace tailWord_1150048 prefixEnd_1150048 131228311053782592358007 := by
  unfold tailWord_1150048
  simp only [CollatzResearch.WordTrace]
  refine ⟨20972848268789991703153399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27963797691719988937537865 20972848268789991703153399)
  ·
    refine ⟨31459272403184987554730099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20972848268789991703153399 31459272403184987554730099)
    ·
      refine ⟨47188908604777481332095149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31459272403184987554730099 47188908604777481332095149)
      ·
        refine ⟨17695840726791555499535681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47188908604777481332095149 17695840726791555499535681)
        ·
          refine ⟨13271880545093666624651761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17695840726791555499535681 13271880545093666624651761)
          ·
            refine ⟨9953910408820249968488821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13271880545093666624651761 9953910408820249968488821)
            ·
              refine ⟨933179100826898434545827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9953910408820249968488821 933179100826898434545827)
              ·
                refine ⟨1399768651240347651818741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 933179100826898434545827 1399768651240347651818741)
                ·
                  refine ⟨131228311053782592358007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1399768651240347651818741 131228311053782592358007)
                  ·
                    rfl

theorem cell22_1150048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 5].length) (baseStart_1150048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150048 prefixEnd_1150048 := by exact prefixLift 1150048
  have htrace : WordTrace (prefixWord ++ tailWord_1150048) baseStart_1150048 baseEnd_1150048 := by
    simpa [prefixWord, tailWord_1150048, baseEnd_1150048] using wordTrace_append hprefix tailTrace_1150048
  have hstable : (prefixWord ++ tailWord_1150048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150048).length < 2 ^ (prefixWord ++ tailWord_1150048).sum := by decide
  have hdescent : baseEnd_1150048 < baseStart_1150048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150125 : List Nat := [1, 5, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_1150125 : Nat := 118140960795 + 1150125 * 2 ^ 59
def prefixEnd_1150125 : Nat := 4983230072969 + 3 ^ 40 * 1150125 * 2
def baseEnd_1150125 : Nat := 393711291834945242898785

theorem tailTrace_1150125 : CollatzResearch.WordTrace tailWord_1150125 prefixEnd_1150125 393711291834945242898785 := by
  unfold tailWord_1150125
  simp only [CollatzResearch.WordTrace]
  refine ⟨41948504958301025556859829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27965669972200683704573219 41948504958301025556859829)
  ·
    refine ⟨3932672339840721145955609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41948504958301025556859829 3932672339840721145955609)
    ·
      refine ⟨2949504254880540859466707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3932672339840721145955609 2949504254880540859466707)
      ·
        refine ⟨4424256382320811289200061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2949504254880540859466707 4424256382320811289200061)
        ·
          refine ⟨1659096143370304233450023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4424256382320811289200061 1659096143370304233450023)
          ·
            refine ⟨2488644215055456350175035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1659096143370304233450023 2488644215055456350175035)
            ·
              refine ⟨3732966322583184525262553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2488644215055456350175035 3732966322583184525262553)
              ·
                refine ⟨2799724741937388393946915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3732966322583184525262553 2799724741937388393946915)
                ·
                  refine ⟨4199587112906082590920373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2799724741937388393946915 4199587112906082590920373)
                  ·
                    refine ⟨393711291834945242898785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4199587112906082590920373 393711291834945242898785)
                    ·
                      rfl

theorem cell22_1150125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_1150125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150125 prefixEnd_1150125 := by exact prefixLift 1150125
  have htrace : WordTrace (prefixWord ++ tailWord_1150125) baseStart_1150125 baseEnd_1150125 := by
    simpa [prefixWord, tailWord_1150125, baseEnd_1150125] using wordTrace_append hprefix tailTrace_1150125
  have hstable : (prefixWord ++ tailWord_1150125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150125).length < 2 ^ (prefixWord ++ tailWord_1150125).sum := by decide
  have hdescent : baseEnd_1150125 < baseStart_1150125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150142 : List Nat := [4, 2, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_1150142 : Nat := 118140960795 + 1150142 * 2 ^ 59
def prefixEnd_1150142 : Nat := 4983230072969 + 3 ^ 40 * 1150142 * 2
def baseEnd_1150142 : Nat := 393717111282362865223733

theorem tailTrace_1150142 : CollatzResearch.WordTrace tailWord_1150142 prefixEnd_1150142 393717111282362865223733 := by
  unfold tailWord_1150142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5243640624904929682528585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27966083332826291640152453 5243640624904929682528585)
  ·
    refine ⟨3932730468678697261896439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5243640624904929682528585 3932730468678697261896439)
    ·
      refine ⟨5899095703018045892844659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3932730468678697261896439 5899095703018045892844659)
      ·
        refine ⟨8848643554527068839266989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5899095703018045892844659 8848643554527068839266989)
        ·
          refine ⟨3318241332947650814725121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8848643554527068839266989 3318241332947650814725121)
          ·
            refine ⟨2488680999710738111043841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3318241332947650814725121 2488680999710738111043841)
            ·
              refine ⟨1866510749783053583282881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2488680999710738111043841 1866510749783053583282881)
              ·
                refine ⟨1399883062337290187462161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1866510749783053583282881 1399883062337290187462161)
                ·
                  refine ⟨1049912296752967640596621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1399883062337290187462161 1049912296752967640596621)
                  ·
                    refine ⟨393717111282362865223733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1049912296752967640596621 393717111282362865223733)
                    ·
                      rfl

theorem cell22_1150142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_1150142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150142 prefixEnd_1150142 := by exact prefixLift 1150142
  have htrace : WordTrace (prefixWord ++ tailWord_1150142) baseStart_1150142 baseEnd_1150142 := by
    simpa [prefixWord, tailWord_1150142, baseEnd_1150142] using wordTrace_append hprefix tailTrace_1150142
  have hstable : (prefixWord ++ tailWord_1150142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150142).length < 2 ^ (prefixWord ++ tailWord_1150142).sum := by decide
  have hdescent : baseEnd_1150142 < baseStart_1150142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150144 : List Nat := [2, 1, 1, 2, 7, 1, 2, 2, 4]
def baseStart_1150144 : Nat := 118140960795 + 1150144 * 2 ^ 59
def prefixEnd_1150144 : Nat := 4983230072969 + 3 ^ 40 * 1150144 * 2
def baseEnd_1150144 : Nat := 131239265307745175557909

theorem tailTrace_1150144 : CollatzResearch.WordTrace tailWord_1150144 prefixEnd_1150144 131239265307745175557909 := by
  unfold tailWord_1150144
  simp only [CollatzResearch.WordTrace]
  refine ⟨20974598972616095900900743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27966131963488127867867657 20974598972616095900900743)
  ·
    refine ⟨31461898458924143851351115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20974598972616095900900743 31461898458924143851351115)
    ·
      refine ⟨47192847688386215777026673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31461898458924143851351115 47192847688386215777026673)
      ·
        refine ⟨35394635766289661832770005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47192847688386215777026673 35394635766289661832770005)
        ·
          refine ⟨829561775772413949205547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 35394635766289661832770005 829561775772413949205547)
          ·
            refine ⟨1244342663658620923808321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829561775772413949205547 1244342663658620923808321)
            ·
              refine ⟨933256997743965692856241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1244342663658620923808321 933256997743965692856241)
              ·
                refine ⟨699942748307974269642181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 933256997743965692856241 699942748307974269642181)
                ·
                  refine ⟨131239265307745175557909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 699942748307974269642181 131239265307745175557909)
                  ·
                    rfl

theorem cell22_1150144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 4].length) (baseStart_1150144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150144 prefixEnd_1150144 := by exact prefixLift 1150144
  have htrace : WordTrace (prefixWord ++ tailWord_1150144) baseStart_1150144 baseEnd_1150144 := by
    simpa [prefixWord, tailWord_1150144, baseEnd_1150144] using wordTrace_append hprefix tailTrace_1150144
  have hstable : (prefixWord ++ tailWord_1150144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150144).length < 2 ^ (prefixWord ++ tailWord_1150144).sum := by decide
  have hdescent : baseEnd_1150144 < baseStart_1150144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150187 : List Nat := [1, 1, 1, 1, 2, 7, 2, 3, 1, 3]
def baseStart_1150187 : Nat := 118140960795 + 1150187 * 2 ^ 59
def prefixEnd_1150187 : Nat := 4983230072969 + 3 ^ 40 * 1150187 * 2
def baseEnd_1150187 : Nat := 393732515701997747848595

theorem tailTrace_1150187 : CollatzResearch.WordTrace tailWord_1150187 prefixEnd_1150187 393732515701997747848595 := by
  unfold tailWord_1150187
  simp only [CollatzResearch.WordTrace]
  refine ⟨41950766284076410145616815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27967177522717606763744543 41950766284076410145616815)
  ·
    refine ⟨62926149426114615218425223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41950766284076410145616815 62926149426114615218425223)
    ·
      refine ⟨94389224139171922827637835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62926149426114615218425223 94389224139171922827637835)
      ·
        refine ⟨141583836208757884241456753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94389224139171922827637835 141583836208757884241456753)
        ·
          refine ⟨106187877156568413181092565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141583836208757884241456753 106187877156568413181092565)
          ·
            refine ⟨2488778370857072183931857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 106187877156568413181092565 2488778370857072183931857)
            ·
              refine ⟨1866583778142804137948893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2488778370857072183931857 1866583778142804137948893)
              ·
                refine ⟨699968916803551551730835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1866583778142804137948893 699968916803551551730835)
                ·
                  refine ⟨1049953375205327327596253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 699968916803551551730835 1049953375205327327596253)
                  ·
                    refine ⟨393732515701997747848595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1049953375205327327596253 393732515701997747848595)
                    ·
                      rfl

theorem cell22_1150187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 1, 3].length) (baseStart_1150187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150187 prefixEnd_1150187 := by exact prefixLift 1150187
  have htrace : WordTrace (prefixWord ++ tailWord_1150187) baseStart_1150187 baseEnd_1150187 := by
    simpa [prefixWord, tailWord_1150187, baseEnd_1150187] using wordTrace_append hprefix tailTrace_1150187
  have hstable : (prefixWord ++ tailWord_1150187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150187).length < 2 ^ (prefixWord ++ tailWord_1150187).sum := by decide
  have hdescent : baseEnd_1150187 < baseStart_1150187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150238 : List Nat := [4, 3, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_1150238 : Nat := 118140960795 + 1150238 * 2 ^ 59
def prefixEnd_1150238 : Nat := 4983230072969 + 3 ^ 40 * 1150238 * 2
def baseEnd_1150238 : Nat := 393749974044250614823439

theorem tailTrace_1150238 : CollatzResearch.WordTrace tailWord_1150238 prefixEnd_1150238 393749974044250614823439 := by
  unfold tailWord_1150238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5244078300861455731965421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27968417604594430570482245 5244078300861455731965421)
  ·
    refine ⟨1966529362823045899487033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5244078300861455731965421 1966529362823045899487033)
    ·
      refine ⟨1474897022117284424615275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1966529362823045899487033 1474897022117284424615275)
      ·
        refine ⟨2212345533175926636922913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1474897022117284424615275 2212345533175926636922913)
        ·
          refine ⟨1659259149881944977692185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2212345533175926636922913 1659259149881944977692185)
          ·
            refine ⟨1244444362411458733269139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1659259149881944977692185 1244444362411458733269139)
            ·
              refine ⟨1866666543617188099903709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1244444362411458733269139 1866666543617188099903709)
              ·
                refine ⟨699999953856445537463891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1866666543617188099903709 699999953856445537463891)
                ·
                  refine ⟨1049999930784668306195837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 699999953856445537463891 1049999930784668306195837)
                  ·
                    refine ⟨393749974044250614823439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1049999930784668306195837 393749974044250614823439)
                    ·
                      rfl

theorem cell22_1150238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_1150238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150238 prefixEnd_1150238 := by exact prefixLift 1150238
  have htrace : WordTrace (prefixWord ++ tailWord_1150238) baseStart_1150238 baseEnd_1150238 := by
    simpa [prefixWord, tailWord_1150238, baseEnd_1150238] using wordTrace_append hprefix tailTrace_1150238
  have hstable : (prefixWord ++ tailWord_1150238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150238).length < 2 ^ (prefixWord ++ tailWord_1150238).sum := by decide
  have hdescent : baseEnd_1150238 < baseStart_1150238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150356 : List Nat := [2, 4, 2, 1, 2, 2, 2, 3, 1, 3]
def baseStart_1150356 : Nat := 118140960795 + 1150356 * 2 ^ 59
def prefixEnd_1150356 : Nat := 4983230072969 + 3 ^ 40 * 1150356 * 2
def baseEnd_1150356 : Nat := 393790367855737640373077

theorem tailTrace_1150356 : CollatzResearch.WordTrace tailWord_1150356 prefixEnd_1150356 393790367855737640373077 := by
  unfold tailWord_1150356
  simp only [CollatzResearch.WordTrace]
  refine ⟨20978465110232076004259461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27971286813642768005679281 20978465110232076004259461)
  ·
    refine ⟨3933462208168514250798649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20978465110232076004259461 3933462208168514250798649)
    ·
      refine ⟨2950096656126385688098987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3933462208168514250798649 2950096656126385688098987)
      ·
        refine ⟨4425144984189578532148481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2950096656126385688098987 4425144984189578532148481)
        ·
          refine ⟨3318858738142183899111361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4425144984189578532148481 3318858738142183899111361)
          ·
            refine ⟨2489144053606637924333521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3318858738142183899111361 2489144053606637924333521)
            ·
              refine ⟨1866858040204978443250141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2489144053606637924333521 1866858040204978443250141)
              ·
                refine ⟨700071765076866916218803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1866858040204978443250141 700071765076866916218803)
                ·
                  refine ⟨1050107647615300374328205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700071765076866916218803 1050107647615300374328205)
                  ·
                    refine ⟨393790367855737640373077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1050107647615300374328205 393790367855737640373077)
                    ·
                      rfl

theorem cell22_1150356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_1150356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150356 prefixEnd_1150356 := by exact prefixLift 1150356
  have htrace : WordTrace (prefixWord ++ tailWord_1150356) baseStart_1150356 baseEnd_1150356 := by
    simpa [prefixWord, tailWord_1150356, baseEnd_1150356] using wordTrace_append hprefix tailTrace_1150356
  have hstable : (prefixWord ++ tailWord_1150356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150356).length < 2 ^ (prefixWord ++ tailWord_1150356).sum := by decide
  have hdescent : baseEnd_1150356 < baseStart_1150356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150410 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 1, 6]
def baseStart_1150410 : Nat := 118140960795 + 1150410 * 2 ^ 59
def prefixEnd_1150410 : Nat := 4983230072969 + 3 ^ 40 * 1150410 * 2
def baseEnd_1150410 : Nat := 393808853159299499522911

theorem tailTrace_1150410 : CollatzResearch.WordTrace tailWord_1150410 prefixEnd_1150410 393808853159299499522911 := by
  unfold tailWord_1150410
  simp only [CollatzResearch.WordTrace]
  refine ⟨10489724940567129807746171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27972599841512346153989789 10489724940567129807746171)
  ·
    refine ⟨15734587410850694711619257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10489724940567129807746171 15734587410850694711619257)
    ·
      refine ⟨11800940558138021033714443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15734587410850694711619257 11800940558138021033714443)
      ·
        refine ⟨17701410837207031550571665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11800940558138021033714443 17701410837207031550571665)
        ·
          refine ⟨13276058127905273662928749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17701410837207031550571665 13276058127905273662928749)
          ·
            refine ⟨4978521797964477623598281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13276058127905273662928749 4978521797964477623598281)
            ·
              refine ⟨3733891348473358217698711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4978521797964477623598281 3733891348473358217698711)
              ·
                refine ⟨5600837022710037326548067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3733891348473358217698711 5600837022710037326548067)
                ·
                  refine ⟨8401255534065055989822101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5600837022710037326548067 8401255534065055989822101)
                  ·
                    refine ⟨393808853159299499522911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8401255534065055989822101 393808853159299499522911)
                    ·
                      rfl

theorem cell22_1150410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_1150410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150410 prefixEnd_1150410 := by exact prefixLift 1150410
  have htrace : WordTrace (prefixWord ++ tailWord_1150410) baseStart_1150410 baseEnd_1150410 := by
    simpa [prefixWord, tailWord_1150410, baseEnd_1150410] using wordTrace_append hprefix tailTrace_1150410
  have hstable : (prefixWord ++ tailWord_1150410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150410).length < 2 ^ (prefixWord ++ tailWord_1150410).sum := by decide
  have hdescent : baseEnd_1150410 < baseStart_1150410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150412 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 4, 3]
def baseStart_1150412 : Nat := 118140960795 + 1150412 * 2 ^ 59
def prefixEnd_1150412 : Nat := 4983230072969 + 3 ^ 40 * 1150412 * 2
def baseEnd_1150412 : Nat := 393809537800172160972905

theorem tailTrace_1150412 : CollatzResearch.WordTrace tailWord_1150412 prefixEnd_1150412 393809537800172160972905 := by
  unfold tailWord_1150412
  simp only [CollatzResearch.WordTrace]
  refine ⟨20979486354130636786278745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27972648472174182381704993 20979486354130636786278745)
  ·
    refine ⟨15734614765597977589709059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20979486354130636786278745 15734614765597977589709059)
    ·
      refine ⟨23601922148396966384563589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15734614765597977589709059 23601922148396966384563589)
      ·
        refine ⟨4425360402824431197105673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23601922148396966384563589 4425360402824431197105673)
        ·
          refine ⟨3319020302118323397829255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4425360402824431197105673 3319020302118323397829255)
          ·
            refine ⟨4978530453177485096743883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3319020302118323397829255 4978530453177485096743883)
            ·
              refine ⟨7467795679766227645115825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4978530453177485096743883 7467795679766227645115825)
              ·
                refine ⟨5600846759824670733836869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7467795679766227645115825 5600846759824670733836869)
                ·
                  refine ⟨1050158767467125762594413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5600846759824670733836869 1050158767467125762594413)
                  ·
                    refine ⟨393809537800172160972905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1050158767467125762594413 393809537800172160972905)
                    ·
                      rfl

theorem cell22_1150412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_1150412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150412 prefixEnd_1150412 := by exact prefixLift 1150412
  have htrace : WordTrace (prefixWord ++ tailWord_1150412) baseStart_1150412 baseEnd_1150412 := by
    simpa [prefixWord, tailWord_1150412, baseEnd_1150412] using wordTrace_append hprefix tailTrace_1150412
  have hstable : (prefixWord ++ tailWord_1150412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150412).length < 2 ^ (prefixWord ++ tailWord_1150412).sum := by decide
  have hdescent : baseEnd_1150412 < baseStart_1150412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150425 : List Nat := [1, 2, 1, 2, 4, 4, 8]
def baseStart_1150425 : Nat := 118140960795 + 1150425 * 2 ^ 59
def prefixEnd_1150425 : Nat := 4983230072969 + 3 ^ 40 * 1150425 * 2
def baseEnd_1150425 : Nat := 14585703257994239273995

theorem tailTrace_1150425 : CollatzResearch.WordTrace tailWord_1150425 prefixEnd_1150425 14585703257994239273995 := by
  unfold tailWord_1150425
  simp only [CollatzResearch.WordTrace]
  refine ⟨41959446857214176792780729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27972964571476117861853819 41959446857214176792780729)
  ·
    refine ⟨31469585142910632594585547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41959446857214176792780729 31469585142910632594585547)
    ·
      refine ⟨47204377714365948891878321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31469585142910632594585547 47204377714365948891878321)
      ·
        refine ⟨35403283285774461668908741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47204377714365948891878321 35403283285774461668908741)
        ·
          refine ⟨6638115616082711562920389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35403283285774461668908741 6638115616082711562920389)
          ·
            refine ⟨1244646678015508418047573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6638115616082711562920389 1244646678015508418047573)
            ·
              refine ⟨14585703257994239273995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1244646678015508418047573 14585703257994239273995)
              ·
                rfl

theorem cell22_1150425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 8].length) (baseStart_1150425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150425 prefixEnd_1150425 := by exact prefixLift 1150425
  have htrace : WordTrace (prefixWord ++ tailWord_1150425) baseStart_1150425 baseEnd_1150425 := by
    simpa [prefixWord, tailWord_1150425, baseEnd_1150425] using wordTrace_append hprefix tailTrace_1150425
  have hstable : (prefixWord ++ tailWord_1150425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150425).length < 2 ^ (prefixWord ++ tailWord_1150425).sum := by decide
  have hdescent : baseEnd_1150425 < baseStart_1150425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150442 : List Nat := [3, 1, 3, 1, 4, 1, 2, 7]
def baseStart_1150442 : Nat := 118140960795 + 1150442 * 2 ^ 59
def prefixEnd_1150442 : Nat := 4983230072969 + 3 ^ 40 * 1150442 * 2
def baseEnd_1150442 : Nat := 43757756379251342524757

theorem tailTrace_1150442 : CollatzResearch.WordTrace tailWord_1150442 prefixEnd_1150442 43757756379251342524757 := by
  unfold tailWord_1150442
  simp only [CollatzResearch.WordTrace]
  refine ⟨10490016724538147174037395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27973377932101725797433053 10490016724538147174037395)
  ·
    refine ⟨15735025086807220761056093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10490016724538147174037395 15735025086807220761056093)
    ·
      refine ⟨5900634407552707785396035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15735025086807220761056093 5900634407552707785396035)
      ·
        refine ⟨8850951611329061678094053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5900634407552707785396035 8850951611329061678094053)
        ·
          refine ⟨1659553427124199064642635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8850951611329061678094053 1659553427124199064642635)
          ·
            refine ⟨2489330140686298596963953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1659553427124199064642635 2489330140686298596963953)
            ·
              refine ⟨1866997605514723947722965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2489330140686298596963953 1866997605514723947722965)
              ·
                refine ⟨43757756379251342524757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1866997605514723947722965 43757756379251342524757)
                ·
                  rfl

theorem cell22_1150442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 7].length) (baseStart_1150442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150442 prefixEnd_1150442 := by exact prefixLift 1150442
  have htrace : WordTrace (prefixWord ++ tailWord_1150442) baseStart_1150442 baseEnd_1150442 := by
    simpa [prefixWord, tailWord_1150442, baseEnd_1150442] using wordTrace_append hprefix tailTrace_1150442
  have hstable : (prefixWord ++ tailWord_1150442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150442).length < 2 ^ (prefixWord ++ tailWord_1150442).sum := by decide
  have hdescent : baseEnd_1150442 < baseStart_1150442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150515 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 8]
def baseStart_1150515 : Nat := 118140960795 + 1150515 * 2 ^ 59
def prefixEnd_1150515 : Nat := 4983230072969 + 3 ^ 40 * 1150515 * 2
def baseEnd_1150515 : Nat := 131281598935038075215863

theorem tailTrace_1150515 : CollatzResearch.WordTrace tailWord_1150515 prefixEnd_1150515 131281598935038075215863 := by
  unfold tailWord_1150515
  simp only [CollatzResearch.WordTrace]
  refine ⟨41962729426888122163556999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27975152951258748109037999 41962729426888122163556999)
  ·
    refine ⟨62944094140332183245335499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41962729426888122163556999 62944094140332183245335499)
    ·
      refine ⟨94416141210498274868003249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62944094140332183245335499 94416141210498274868003249)
      ·
        refine ⟨70812105907873706151002437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94416141210498274868003249 70812105907873706151002437)
        ·
          refine ⟨13277269857726319903312957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70812105907873706151002437 13277269857726319903312957)
          ·
            refine ⟨4978976196647369963742359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13277269857726319903312957 4978976196647369963742359)
            ·
              refine ⟨7468464294971054945613539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4978976196647369963742359 7468464294971054945613539)
              ·
                refine ⟨11202696442456582418420309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7468464294971054945613539 11202696442456582418420309)
                ·
                  refine ⟨131281598935038075215863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11202696442456582418420309 131281598935038075215863)
                  ·
                    rfl

theorem cell22_1150515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 8].length) (baseStart_1150515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150515 prefixEnd_1150515 := by exact prefixLift 1150515
  have htrace : WordTrace (prefixWord ++ tailWord_1150515) baseStart_1150515 baseEnd_1150515 := by
    simpa [prefixWord, tailWord_1150515, baseEnd_1150515] using wordTrace_append hprefix tailTrace_1150515
  have hstable : (prefixWord ++ tailWord_1150515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150515).length < 2 ^ (prefixWord ++ tailWord_1150515).sum := by decide
  have hdescent : baseEnd_1150515 < baseStart_1150515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150517 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 3, 4]
def baseStart_1150517 : Nat := 118140960795 + 1150517 * 2 ^ 59
def prefixEnd_1150517 : Nat := 4983230072969 + 3 ^ 40 * 1150517 * 2
def baseEnd_1150517 : Nat := 393845481445986887097583

theorem tailTrace_1150517 : CollatzResearch.WordTrace tailWord_1150517 prefixEnd_1150517 393845481445986887097583 := by
  unfold tailWord_1150517
  simp only [CollatzResearch.WordTrace]
  refine ⟨41962802372880876505129805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27975201581920584336753203 41962802372880876505129805)
  ·
    refine ⟨15736050889830328689423677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41962802372880876505129805 15736050889830328689423677)
    ·
      refine ⟨5901019083686373258533879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15736050889830328689423677 5901019083686373258533879)
      ·
        refine ⟨8851528625529559887800819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5901019083686373258533879 8851528625529559887800819)
        ·
          refine ⟨13277292938294339831701229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8851528625529559887800819 13277292938294339831701229)
          ·
            refine ⟨4978984851860377436887961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13277292938294339831701229 4978984851860377436887961)
            ·
              refine ⟨3734238638895283077665971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4978984851860377436887961 3734238638895283077665971)
              ·
                refine ⟨5601357958342924616498957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3734238638895283077665971 5601357958342924616498957)
                ·
                  refine ⟨2100509234378596731187109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5601357958342924616498957 2100509234378596731187109)
                  ·
                    refine ⟨393845481445986887097583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2100509234378596731187109 393845481445986887097583)
                    ·
                      rfl

theorem cell22_1150517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_1150517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150517 prefixEnd_1150517 := by exact prefixLift 1150517
  have htrace : WordTrace (prefixWord ++ tailWord_1150517) baseStart_1150517 baseEnd_1150517 := by
    simpa [prefixWord, tailWord_1150517, baseEnd_1150517] using wordTrace_append hprefix tailTrace_1150517
  have hstable : (prefixWord ++ tailWord_1150517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150517).length < 2 ^ (prefixWord ++ tailWord_1150517).sum := by decide
  have hdescent : baseEnd_1150517 < baseStart_1150517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150560 : List Nat := [2, 1, 1, 3, 2, 1, 1, 11]
def baseStart_1150560 : Nat := 118140960795 + 1150560 * 2 ^ 59
def prefixEnd_1150560 : Nat := 4983230072969 + 3 ^ 40 * 1150560 * 2
def baseEnd_1150560 : Nat := 43762244580527678696939

theorem tailTrace_1150560 : CollatzResearch.WordTrace tailWord_1150560 prefixEnd_1150560 43762244580527678696939 := by
  unfold tailWord_1150560
  simp only [CollatzResearch.WordTrace]
  refine ⟨20982185355862547424472567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27976247141150063232630089 20982185355862547424472567)
  ·
    refine ⟨31473278033793821136708851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20982185355862547424472567 31473278033793821136708851)
    ·
      refine ⟨47209917050690731705063277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31473278033793821136708851 47209917050690731705063277)
      ·
        refine ⟨17703718894009024389398729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47209917050690731705063277 17703718894009024389398729)
        ·
          refine ⟨13277789170506768292049047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17703718894009024389398729 13277789170506768292049047)
          ·
            refine ⟨19916683755760152438073571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13277789170506768292049047 19916683755760152438073571)
            ·
              refine ⟨29875025633640228657110357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19916683755760152438073571 29875025633640228657110357)
              ·
                refine ⟨43762244580527678696939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 29875025633640228657110357 43762244580527678696939)
                ·
                  rfl

theorem cell22_1150560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 11].length) (baseStart_1150560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150560 prefixEnd_1150560 := by exact prefixLift 1150560
  have htrace : WordTrace (prefixWord ++ tailWord_1150560) baseStart_1150560 baseEnd_1150560 := by
    simpa [prefixWord, tailWord_1150560, baseEnd_1150560] using wordTrace_append hprefix tailTrace_1150560
  have hstable : (prefixWord ++ tailWord_1150560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150560).length < 2 ^ (prefixWord ++ tailWord_1150560).sum := by decide
  have hdescent : baseEnd_1150560 < baseStart_1150560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150564 : List Nat := [2, 3, 1, 1, 2, 5, 1, 1, 1, 5]
def baseStart_1150564 : Nat := 118140960795 + 1150564 * 2 ^ 59
def prefixEnd_1150564 : Nat := 4983230072969 + 3 ^ 40 * 1150564 * 2
def baseEnd_1150564 : Nat := 393861570506494431172439

theorem tailTrace_1150564 : CollatzResearch.WordTrace tailWord_1150564 prefixEnd_1150564 393861570506494431172439 := by
  unfold tailWord_1150564
  simp only [CollatzResearch.WordTrace]
  refine ⟨20982258301855301766045373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27976344402473735688060497 20982258301855301766045373)
  ·
    refine ⟨7868346863195738162267015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20982258301855301766045373 7868346863195738162267015)
    ·
      refine ⟨11802520294793607243400523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7868346863195738162267015 11802520294793607243400523)
      ·
        refine ⟨17703780442190410865100785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11802520294793607243400523 17703780442190410865100785)
        ·
          refine ⟨13277835331642808148825589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17703780442190410865100785 13277835331642808148825589)
          ·
            refine ⟨1244797062341513263952399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13277835331642808148825589 1244797062341513263952399)
            ·
              refine ⟨1867195593512269895928599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1244797062341513263952399 1867195593512269895928599)
              ·
                refine ⟨2800793390268404843892899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1867195593512269895928599 2800793390268404843892899)
                ·
                  refine ⟨4201190085402607265839349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2800793390268404843892899 4201190085402607265839349)
                  ·
                    refine ⟨393861570506494431172439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4201190085402607265839349 393861570506494431172439)
                    ·
                      rfl

theorem cell22_1150564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_1150564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150564 prefixEnd_1150564 := by exact prefixLift 1150564
  have htrace : WordTrace (prefixWord ++ tailWord_1150564) baseStart_1150564 baseEnd_1150564 := by
    simpa [prefixWord, tailWord_1150564, baseEnd_1150564] using wordTrace_append hprefix tailTrace_1150564
  have hstable : (prefixWord ++ tailWord_1150564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150564).length < 2 ^ (prefixWord ++ tailWord_1150564).sum := by decide
  have hdescent : baseEnd_1150564 < baseStart_1150564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150575 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 1, 9]
def baseStart_1150575 : Nat := 118140960795 + 1150575 * 2 ^ 59
def prefixEnd_1150575 : Nat := 4983230072969 + 3 ^ 40 * 1150575 * 2
def baseEnd_1150575 : Nat := 393865336031294069147405

theorem tailTrace_1150575 : CollatzResearch.WordTrace tailWord_1150575 prefixEnd_1150575 393865336031294069147405 := by
  unfold tailWord_1150575
  simp only [CollatzResearch.WordTrace]
  refine ⟨41964917806670752410741179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27976611871113834940494119 41964917806670752410741179)
  ·
    refine ⟨62947376710006128616111769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41964917806670752410741179 62947376710006128616111769)
    ·
      refine ⟨47210532532504596462083827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62947376710006128616111769 47210532532504596462083827)
      ·
        refine ⟨70815798798756894693125741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47210532532504596462083827 70815798798756894693125741)
        ·
          refine ⟨26555924549533835509922153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70815798798756894693125741 26555924549533835509922153)
          ·
            refine ⟨19916943412150376632441615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26555924549533835509922153 19916943412150376632441615)
            ·
              refine ⟨29875415118225564948662423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19916943412150376632441615 29875415118225564948662423)
              ·
                refine ⟨44813122677338347422993635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29875415118225564948662423 44813122677338347422993635)
                ·
                  refine ⟨67219684016007521134490453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44813122677338347422993635 67219684016007521134490453)
                  ·
                    refine ⟨393865336031294069147405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 67219684016007521134490453 393865336031294069147405)
                    ·
                      rfl

theorem cell22_1150575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_1150575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150575 prefixEnd_1150575 := by exact prefixLift 1150575
  have htrace : WordTrace (prefixWord ++ tailWord_1150575) baseStart_1150575 baseEnd_1150575 := by
    simpa [prefixWord, tailWord_1150575, baseEnd_1150575] using wordTrace_append hprefix tailTrace_1150575
  have hstable : (prefixWord ++ tailWord_1150575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150575).length < 2 ^ (prefixWord ++ tailWord_1150575).sum := by decide
  have hdescent : baseEnd_1150575 < baseStart_1150575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150701 : List Nat := [1, 5, 1, 2, 1, 2, 1, 5, 4]
def baseStart_1150701 : Nat := 118140960795 + 1150701 * 2 ^ 59
def prefixEnd_1150701 : Nat := 4983230072969 + 3 ^ 40 * 1150701 * 2
def baseEnd_1150701 : Nat := 131302822802090580165673

theorem tailTrace_1150701 : CollatzResearch.WordTrace tailWord_1150701 prefixEnd_1150701 131302822802090580165673 := by
  unfold tailWord_1150701
  simp only [CollatzResearch.WordTrace]
  refine ⟨41969513404214275929827957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27979675602809517286551971 41969513404214275929827957)
  ·
    refine ⟨3934641881645088368421371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41969513404214275929827957 3934641881645088368421371)
    ·
      refine ⟨5901962822467632552632057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3934641881645088368421371 5901962822467632552632057)
      ·
        refine ⟨4426472116850724414474043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5901962822467632552632057 4426472116850724414474043)
        ·
          refine ⟨6639708175276086621711065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4426472116850724414474043 6639708175276086621711065)
          ·
            refine ⟨4979781131457064966283299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6639708175276086621711065 4979781131457064966283299)
            ·
              refine ⟨7469671697185597449424949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4979781131457064966283299 7469671697185597449424949)
              ·
                refine ⟨700281721611149760883589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7469671697185597449424949 700281721611149760883589)
                ·
                  refine ⟨131302822802090580165673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 700281721611149760883589 131302822802090580165673)
                  ·
                    rfl

theorem cell22_1150701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_1150701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150701 prefixEnd_1150701 := by exact prefixLift 1150701
  have htrace : WordTrace (prefixWord ++ tailWord_1150701) baseStart_1150701 baseEnd_1150701 := by
    simpa [prefixWord, tailWord_1150701, baseEnd_1150701] using wordTrace_append hprefix tailTrace_1150701
  have hstable : (prefixWord ++ tailWord_1150701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150701).length < 2 ^ (prefixWord ++ tailWord_1150701).sum := by decide
  have hdescent : baseEnd_1150701 < baseStart_1150701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150746 : List Nat := [3, 1, 1, 3, 2, 4, 2, 6]
def baseStart_1150746 : Nat := 118140960795 + 1150746 * 2 ^ 59
def prefixEnd_1150746 : Nat := 4983230072969 + 3 ^ 40 * 1150746 * 2
def baseEnd_1150746 : Nat := 43769319202878513680209

theorem tailTrace_1150746 : CollatzResearch.WordTrace tailWord_1150746 prefixEnd_1150746 43769319202878513680209 := by
  unfold tailWord_1150746
  simp only [CollatzResearch.WordTrace]
  refine ⟨10492788672262812153804023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27980769792700832410144061 10492788672262812153804023)
  ·
    refine ⟨15739183008394218230706035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10492788672262812153804023 15739183008394218230706035)
    ·
      refine ⟨23608774512591327346059053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15739183008394218230706035 23608774512591327346059053)
      ·
        refine ⟨8853290442221747754772145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23608774512591327346059053 8853290442221747754772145)
        ·
          refine ⟨6639967831666310816079109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8853290442221747754772145 6639967831666310816079109)
          ·
            refine ⟨1244993968437433278014833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6639967831666310816079109 1244993968437433278014833)
            ·
              refine ⟨933745476328074958511125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1244993968437433278014833 933745476328074958511125)
              ·
                refine ⟨43769319202878513680209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 933745476328074958511125 43769319202878513680209)
                ·
                  rfl

theorem cell22_1150746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 6].length) (baseStart_1150746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150746 prefixEnd_1150746 := by exact prefixLift 1150746
  have htrace : WordTrace (prefixWord ++ tailWord_1150746) baseStart_1150746 baseEnd_1150746 := by
    simpa [prefixWord, tailWord_1150746, baseEnd_1150746] using wordTrace_append hprefix tailTrace_1150746
  have hstable : (prefixWord ++ tailWord_1150746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150746).length < 2 ^ (prefixWord ++ tailWord_1150746).sum := by decide
  have hdescent : baseEnd_1150746 < baseStart_1150746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150778 : List Nat := [3, 1, 1, 1, 5, 3, 1, 1, 3, 3]
def baseStart_1150778 : Nat := 118140960795 + 1150778 * 2 ^ 59
def prefixEnd_1150778 : Nat := 4983230072969 + 3 ^ 40 * 1150778 * 2
def baseEnd_1150778 : Nat := 393934827079869206321783

theorem tailTrace_1150778 : CollatzResearch.WordTrace tailWord_1150778 prefixEnd_1150778 393934827079869206321783 := by
  unfold tailWord_1150778
  simp only [CollatzResearch.WordTrace]
  refine ⟨10493080456233829520095247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27981547883290212053587325 10493080456233829520095247)
  ·
    refine ⟨15739620684350744280142871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10493080456233829520095247 15739620684350744280142871)
    ·
      refine ⟨23609431026526116420214307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15739620684350744280142871 23609431026526116420214307)
      ·
        refine ⟨35414146539789174630321461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23609431026526116420214307 35414146539789174630321461)
        ·
          refine ⟨3320076238105235121592637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35414146539789174630321461 3320076238105235121592637)
          ·
            refine ⟨1245028589289463170597239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3320076238105235121592637 1245028589289463170597239)
            ·
              refine ⟨1867542883934194755895859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1245028589289463170597239 1867542883934194755895859)
              ·
                refine ⟨2801314325901292133843789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1867542883934194755895859 2801314325901292133843789)
                ·
                  refine ⟨1050492872212984550191421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2801314325901292133843789 1050492872212984550191421)
                  ·
                    refine ⟨393934827079869206321783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1050492872212984550191421 393934827079869206321783)
                    ·
                      rfl

theorem cell22_1150778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_1150778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150778 prefixEnd_1150778 := by exact prefixLift 1150778
  have htrace : WordTrace (prefixWord ++ tailWord_1150778) baseStart_1150778 baseEnd_1150778 := by
    simpa [prefixWord, tailWord_1150778, baseEnd_1150778] using wordTrace_append hprefix tailTrace_1150778
  have hstable : (prefixWord ++ tailWord_1150778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150778).length < 2 ^ (prefixWord ++ tailWord_1150778).sum := by decide
  have hdescent : baseEnd_1150778 < baseStart_1150778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150791 : List Nat := [1, 1, 4, 1, 2, 1, 6, 1, 5]
def baseStart_1150791 : Nat := 118140960795 + 1150791 * 2 ^ 59
def prefixEnd_1150791 : Nat := 4983230072969 + 3 ^ 40 * 1150791 * 2
def baseEnd_1150791 : Nat := 131313092415180501915581

theorem tailTrace_1150791 : CollatzResearch.WordTrace tailWord_1150791 prefixEnd_1150791 131313092415180501915581 := by
  unfold tailWord_1150791
  simp only [CollatzResearch.WordTrace]
  refine ⟨41972795973888221300604227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27981863982592147533736151 41972795973888221300604227)
  ·
    refine ⟨62959193960832331950906341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41972795973888221300604227 62959193960832331950906341)
    ·
      refine ⟨11804848867656062240794939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62959193960832331950906341 11804848867656062240794939)
      ·
        refine ⟨17707273301484093361192409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11804848867656062240794939 17707273301484093361192409)
        ·
          refine ⟨13280454976113070020894307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17707273301484093361192409 13280454976113070020894307)
          ·
            refine ⟨19920682464169605031341461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13280454976113070020894307 19920682464169605031341461)
            ·
              refine ⟨933781990507950235844131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19920682464169605031341461 933781990507950235844131)
              ·
                refine ⟨1400672985761925353766197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 933781990507950235844131 1400672985761925353766197)
                ·
                  refine ⟨131313092415180501915581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1400672985761925353766197 131313092415180501915581)
                  ·
                    rfl

theorem cell22_1150791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 5].length) (baseStart_1150791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150791 prefixEnd_1150791 := by exact prefixLift 1150791
  have htrace : WordTrace (prefixWord ++ tailWord_1150791) baseStart_1150791 baseEnd_1150791 := by
    simpa [prefixWord, tailWord_1150791, baseEnd_1150791] using wordTrace_append hprefix tailTrace_1150791
  have hstable : (prefixWord ++ tailWord_1150791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150791).length < 2 ^ (prefixWord ++ tailWord_1150791).sum := by decide
  have hdescent : baseEnd_1150791 < baseStart_1150791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150834 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_1150834 : Nat := 118140960795 + 1150834 * 2 ^ 59
def prefixEnd_1150834 : Nat := 4983230072969 + 3 ^ 40 * 1150834 * 2
def baseEnd_1150834 : Nat := 393953997024303726921611

theorem tailTrace_1150834 : CollatzResearch.WordTrace tailWord_1150834 prefixEnd_1150834 393953997024303726921611 := by
  unfold tailWord_1150834
  simp only [CollatzResearch.WordTrace]
  refine ⟨10493591078183109911104889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27982909541821626429613037 10493591078183109911104889)
  ·
    refine ⟨7870193308637332433328667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10493591078183109911104889 7870193308637332433328667)
    ·
      refine ⟨11805289962955998649993001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7870193308637332433328667 11805289962955998649993001)
      ·
        refine ⟨8853967472216998987494751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11805289962955998649993001 8853967472216998987494751)
        ·
          refine ⟨13280951208325498481242127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8853967472216998987494751 13280951208325498481242127)
          ·
            refine ⟨19921426812488247721863191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13280951208325498481242127 19921426812488247721863191)
            ·
              refine ⟨29882140218732371582794787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19921426812488247721863191 29882140218732371582794787)
              ·
                refine ⟨44823210328098557374192181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29882140218732371582794787 44823210328098557374192181)
                ·
                  refine ⟨4202175968259239753830517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44823210328098557374192181 4202175968259239753830517)
                  ·
                    refine ⟨393953997024303726921611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4202175968259239753830517 393953997024303726921611)
                    ·
                      rfl

theorem cell22_1150834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_1150834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150834 prefixEnd_1150834 := by exact prefixLift 1150834
  have htrace : WordTrace (prefixWord ++ tailWord_1150834) baseStart_1150834 baseEnd_1150834 := by
    simpa [prefixWord, tailWord_1150834, baseEnd_1150834] using wordTrace_append hprefix tailTrace_1150834
  have hstable : (prefixWord ++ tailWord_1150834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150834).length < 2 ^ (prefixWord ++ tailWord_1150834).sum := by decide
  have hdescent : baseEnd_1150834 < baseStart_1150834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150851 : List Nat := [1, 1, 1, 3, 4, 3, 2, 1, 1, 5]
def baseStart_1150851 : Nat := 118140960795 + 1150851 * 2 ^ 59
def prefixEnd_1150851 : Nat := 4983230072969 + 3 ^ 40 * 1150851 * 2
def baseEnd_1150851 : Nat := 393959816471721349246559

theorem tailTrace_1150851 : CollatzResearch.WordTrace tailWord_1150851 prefixEnd_1150851 393959816471721349246559 := by
  unfold tailWord_1150851
  simp only [CollatzResearch.WordTrace]
  refine ⟨41974984353670851547788407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27983322902447234365192271 41974984353670851547788407)
  ·
    refine ⟨62962476530506277321682611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41974984353670851547788407 62962476530506277321682611)
    ·
      refine ⟨94443714795759415982523917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62962476530506277321682611 94443714795759415982523917)
      ·
        refine ⟨35416393048409780993446469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94443714795759415982523917 35416393048409780993446469)
        ·
          refine ⟨6640573696576833936271213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35416393048409780993446469 6640573696576833936271213)
          ·
            refine ⟨2490215136216312726101705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6640573696576833936271213 2490215136216312726101705)
            ·
              refine ⟨1867661352162234544576279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2490215136216312726101705 1867661352162234544576279)
              ·
                refine ⟨2801492028243351816864419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1867661352162234544576279 2801492028243351816864419)
                ·
                  refine ⟨4202238042365027725296629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2801492028243351816864419 4202238042365027725296629)
                  ·
                    refine ⟨393959816471721349246559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4202238042365027725296629 393959816471721349246559)
                    ·
                      rfl

theorem cell22_1150851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 5].length) (baseStart_1150851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150851 prefixEnd_1150851 := by exact prefixLift 1150851
  have htrace : WordTrace (prefixWord ++ tailWord_1150851) baseStart_1150851 baseEnd_1150851 := by
    simpa [prefixWord, tailWord_1150851, baseEnd_1150851] using wordTrace_append hprefix tailTrace_1150851
  have hstable : (prefixWord ++ tailWord_1150851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150851).length < 2 ^ (prefixWord ++ tailWord_1150851).sum := by decide
  have hdescent : baseEnd_1150851 < baseStart_1150851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150872 : List Nat := [2, 1, 2, 6, 1, 2, 2, 1, 1, 4]
def baseStart_1150872 : Nat := 118140960795 + 1150872 * 2 ^ 59
def prefixEnd_1150872 : Nat := 4983230072969 + 3 ^ 40 * 1150872 * 2
def baseEnd_1150872 : Nat := 393967005200884294471495

theorem tailTrace_1150872 : CollatzResearch.WordTrace tailWord_1150872 prefixEnd_1150872 393967005200884294471495 := by
  unfold tailWord_1150872
  simp only [CollatzResearch.WordTrace]
  refine ⟨20987875143297386067151435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27983833524396514756201913 20987875143297386067151435)
  ·
    refine ⟨31481812714946079100727153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20987875143297386067151435 31481812714946079100727153)
    ·
      refine ⟨23611359536209559325545365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31481812714946079100727153 23611359536209559325545365)
      ·
        refine ⟨1106782478259823093384939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23611359536209559325545365 1106782478259823093384939)
        ·
          refine ⟨1660173717389734640077409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1106782478259823093384939 1660173717389734640077409)
          ·
            refine ⟨1245130288042300980058057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1660173717389734640077409 1245130288042300980058057)
            ·
              refine ⟨933847716031725735043543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1245130288042300980058057 933847716031725735043543)
              ·
                refine ⟨1400771574047588602565315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 933847716031725735043543 1400771574047588602565315)
                ·
                  refine ⟨2101157361071382903847973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1400771574047588602565315 2101157361071382903847973)
                  ·
                    refine ⟨393967005200884294471495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2101157361071382903847973 393967005200884294471495)
                    ·
                      rfl

theorem cell22_1150872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 1, 4].length) (baseStart_1150872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150872 prefixEnd_1150872 := by exact prefixLift 1150872
  have htrace : WordTrace (prefixWord ++ tailWord_1150872) baseStart_1150872 baseEnd_1150872 := by
    simpa [prefixWord, tailWord_1150872, baseEnd_1150872] using wordTrace_append hprefix tailTrace_1150872
  have hstable : (prefixWord ++ tailWord_1150872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150872).length < 2 ^ (prefixWord ++ tailWord_1150872).sum := by decide
  have hdescent : baseEnd_1150872 < baseStart_1150872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150881 : List Nat := [1, 2, 3, 4, 2, 1, 9]
def baseStart_1150881 : Nat := 118140960795 + 1150881 * 2 ^ 59
def prefixEnd_1150881 : Nat := 4983230072969 + 3 ^ 40 * 1150881 * 2
def baseEnd_1150881 : Nat := 14591484669807824851721

theorem tailTrace_1150881 : CollatzResearch.WordTrace tailWord_1150881 prefixEnd_1150881 14591484669807824851721 := by
  unfold tailWord_1150881
  simp only [CollatzResearch.WordTrace]
  refine ⟨41976078543562166671380497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27984052362374777780920331 41976078543562166671380497)
  ·
    refine ⟨31482058907671625003535373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41976078543562166671380497 31482058907671625003535373)
    ·
      refine ⟨11805772090376859376325765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31482058907671625003535373 11805772090376859376325765)
      ·
        refine ⟨2213582266945661133061081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11805772090376859376325765 2213582266945661133061081)
        ·
          refine ⟨1660186700209245849795811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2213582266945661133061081 1660186700209245849795811)
          ·
            refine ⟨2490280050313868774693717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1660186700209245849795811 2490280050313868774693717)
            ·
              refine ⟨14591484669807824851721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2490280050313868774693717 14591484669807824851721)
              ·
                rfl

theorem cell22_1150881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 9].length) (baseStart_1150881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150881 prefixEnd_1150881 := by exact prefixLift 1150881
  have htrace : WordTrace (prefixWord ++ tailWord_1150881) baseStart_1150881 baseEnd_1150881 := by
    simpa [prefixWord, tailWord_1150881, baseEnd_1150881] using wordTrace_append hprefix tailTrace_1150881
  have hstable : (prefixWord ++ tailWord_1150881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150881).length < 2 ^ (prefixWord ++ tailWord_1150881).sum := by decide
  have hdescent : baseEnd_1150881 < baseStart_1150881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150947 : List Nat := [1, 1, 1, 6, 1, 3, 3, 2, 1, 3]
def baseStart_1150947 : Nat := 118140960795 + 1150947 * 2 ^ 59
def prefixEnd_1150947 : Nat := 4983230072969 + 3 ^ 40 * 1150947 * 2
def baseEnd_1150947 : Nat := 393992679233609098846265

theorem tailTrace_1150947 : CollatzResearch.WordTrace tailWord_1150947 prefixEnd_1150947 393992679233609098846265 := by
  unfold tailWord_1150947
  simp only [CollatzResearch.WordTrace]
  refine ⟨41978485761323059943283095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27985657174215373295522063 41978485761323059943283095)
  ·
    refine ⟨62967728641984589914924643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41978485761323059943283095 62967728641984589914924643)
    ·
      refine ⟨94451592962976884872386965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62967728641984589914924643 94451592962976884872386965)
      ·
        refine ⟨4427418420139541478393139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 94451592962976884872386965 4427418420139541478393139)
        ·
          refine ⟨6641127630209312217589709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4427418420139541478393139 6641127630209312217589709)
          ·
            refine ⟨2490422861328492081596141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6641127630209312217589709 2490422861328492081596141)
            ·
              refine ⟨933908572998184530598553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2490422861328492081596141 933908572998184530598553)
              ·
                refine ⟨700431429748638397948915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 933908572998184530598553 700431429748638397948915)
                ·
                  refine ⟨1050647144622957596923373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700431429748638397948915 1050647144622957596923373)
                  ·
                    refine ⟨393992679233609098846265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1050647144622957596923373 393992679233609098846265)
                    ·
                      rfl

theorem cell22_1150947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 1, 3].length) (baseStart_1150947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150947 prefixEnd_1150947 := by exact prefixLift 1150947
  have htrace : WordTrace (prefixWord ++ tailWord_1150947) baseStart_1150947 baseEnd_1150947 := by
    simpa [prefixWord, tailWord_1150947, baseEnd_1150947] using wordTrace_append hprefix tailTrace_1150947
  have hstable : (prefixWord ++ tailWord_1150947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150947).length < 2 ^ (prefixWord ++ tailWord_1150947).sum := by decide
  have hdescent : baseEnd_1150947 < baseStart_1150947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150973 : List Nat := [1, 4, 1, 1, 1, 2, 5, 2, 1, 4]
def baseStart_1150973 : Nat := 118140960795 + 1150973 * 2 ^ 59
def prefixEnd_1150973 : Nat := 4983230072969 + 3 ^ 40 * 1150973 * 2
def baseEnd_1150973 : Nat := 394001579564953697696185

theorem tailTrace_1150973 : CollatzResearch.WordTrace tailWord_1150973 prefixEnd_1150973 394001579564953697696185 := by
  unfold tailWord_1150973
  simp only [CollatzResearch.WordTrace]
  refine ⟨41979434059228866383729573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27986289372819244255819715 41979434059228866383729573)
  ·
    refine ⟨7871143886105412446949295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41979434059228866383729573 7871143886105412446949295)
    ·
      refine ⟨11806715829158118670423943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7871143886105412446949295 11806715829158118670423943)
      ·
        refine ⟨17710073743737178005635915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11806715829158118670423943 17710073743737178005635915)
        ·
          refine ⟨26565110615605767008453873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17710073743737178005635915 26565110615605767008453873)
          ·
            refine ⟨19923832961704325256340405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26565110615605767008453873 19923832961704325256340405)
            ·
              refine ⟨1867859340159780492781913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19923832961704325256340405 1867859340159780492781913)
              ·
                refine ⟨1400894505119835369586435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1867859340159780492781913 1400894505119835369586435)
                ·
                  refine ⟨2101341757679753054379653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1400894505119835369586435 2101341757679753054379653)
                  ·
                    refine ⟨394001579564953697696185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2101341757679753054379653 394001579564953697696185)
                    ·
                      rfl

theorem cell22_1150973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_1150973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150973 prefixEnd_1150973 := by exact prefixLift 1150973
  have htrace : WordTrace (prefixWord ++ tailWord_1150973) baseStart_1150973 baseEnd_1150973 := by
    simpa [prefixWord, tailWord_1150973, baseEnd_1150973] using wordTrace_append hprefix tailTrace_1150973
  have hstable : (prefixWord ++ tailWord_1150973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150973).length < 2 ^ (prefixWord ++ tailWord_1150973).sum := by decide
  have hdescent : baseEnd_1150973 < baseStart_1150973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150988 : List Nat := [2, 2, 1, 2, 3, 1, 2, 5, 4]
def baseStart_1150988 : Nat := 118140960795 + 1150988 * 2 ^ 59
def prefixEnd_1150988 : Nat := 4983230072969 + 3 ^ 40 * 1150988 * 2
def baseEnd_1150988 : Nat := 131335571457166219523713

theorem tailTrace_1150988 : CollatzResearch.WordTrace tailWord_1150988 prefixEnd_1150988 131335571457166219523713 := by
  unfold tailWord_1150988
  simp only [CollatzResearch.WordTrace]
  refine ⟨20989990577087261972762809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27986654102783015963683745 20989990577087261972762809)
  ·
    refine ⟨15742492932815446479572107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20989990577087261972762809 15742492932815446479572107)
    ·
      refine ⟨23613739399223169719358161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15742492932815446479572107 23613739399223169719358161)
      ·
        refine ⟨17710304549417377289518621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23613739399223169719358161 17710304549417377289518621)
        ·
          refine ⟨6641364206031516483569483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17710304549417377289518621 6641364206031516483569483)
          ·
            refine ⟨9962046309047274725354225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6641364206031516483569483 9962046309047274725354225)
            ·
              refine ⟨7471534731785456044015669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9962046309047274725354225 7471534731785456044015669)
              ·
                refine ⟨700456381104886504126469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7471534731785456044015669 700456381104886504126469)
                ·
                  refine ⟨131335571457166219523713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 700456381104886504126469 131335571457166219523713)
                  ·
                    rfl

theorem cell22_1150988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 4].length) (baseStart_1150988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150988 prefixEnd_1150988 := by exact prefixLift 1150988
  have htrace : WordTrace (prefixWord ++ tailWord_1150988) baseStart_1150988 baseEnd_1150988 := by
    simpa [prefixWord, tailWord_1150988, baseEnd_1150988] using wordTrace_append hprefix tailTrace_1150988
  have hstable : (prefixWord ++ tailWord_1150988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150988).length < 2 ^ (prefixWord ++ tailWord_1150988).sum := by decide
  have hdescent : baseEnd_1150988 < baseStart_1150988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150990 : List Nat := [4, 1, 1, 2, 2, 1, 5, 1, 1, 4]
def baseStart_1150990 : Nat := 118140960795 + 1150990 * 2 ^ 59
def prefixEnd_1150990 : Nat := 4983230072969 + 3 ^ 40 * 1150990 * 2
def baseEnd_1150990 : Nat := 394007399012371320021133

theorem tailTrace_1150990 : CollatzResearch.WordTrace tailWord_1150990 prefixEnd_1150990 394007399012371320021133 := by
  unfold tailWord_1150990
  simp only [CollatzResearch.WordTrace]
  refine ⟨5247506762520909785887303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27986702733444852191398949 5247506762520909785887303)
  ·
    refine ⟨7871260143781364678830955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5247506762520909785887303 7871260143781364678830955)
    ·
      refine ⟨11806890215672047018246433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7871260143781364678830955 11806890215672047018246433)
      ·
        refine ⟨8855167661754035263684825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11806890215672047018246433 8855167661754035263684825)
        ·
          refine ⟨6641375746315526447763619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8855167661754035263684825 6641375746315526447763619)
          ·
            refine ⟨9962063619473289671645429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6641375746315526447763619 9962063619473289671645429)
            ·
              refine ⟨933943464325620906716759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9962063619473289671645429 933943464325620906716759)
              ·
                refine ⟨1400915196488431360075139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 933943464325620906716759 1400915196488431360075139)
                ·
                  refine ⟨2101372794732647040112709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1400915196488431360075139 2101372794732647040112709)
                  ·
                    refine ⟨394007399012371320021133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2101372794732647040112709 394007399012371320021133)
                    ·
                      rfl

theorem cell22_1150990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_1150990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1150990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1150990 prefixEnd_1150990 := by exact prefixLift 1150990
  have htrace : WordTrace (prefixWord ++ tailWord_1150990) baseStart_1150990 baseEnd_1150990 := by
    simpa [prefixWord, tailWord_1150990, baseEnd_1150990] using wordTrace_append hprefix tailTrace_1150990
  have hstable : (prefixWord ++ tailWord_1150990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150990).length < 2 ^ (prefixWord ++ tailWord_1150990).sum := by decide
  have hdescent : baseEnd_1150990 < baseStart_1150990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151005 : List Nat := [1, 4, 2, 2, 2, 2, 1, 4, 4]
def baseStart_1151005 : Nat := 118140960795 + 1151005 * 2 ^ 59
def prefixEnd_1151005 : Nat := 4983230072969 + 3 ^ 40 * 1151005 * 2
def baseEnd_1151005 : Nat := 131337511272972093632029

theorem tailTrace_1151005 : CollatzResearch.WordTrace tailWord_1151005 prefixEnd_1151005 131337511272972093632029 := by
  unfold tailWord_1151005
  simp only [CollatzResearch.WordTrace]
  refine ⟨41980601195112935848894469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27987067463408623899262979 41980601195112935848894469)
  ·
    refine ⟨7871362724083675471667713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41980601195112935848894469 7871362724083675471667713)
    ·
      refine ⟨5903522043062756603750785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7871362724083675471667713 5903522043062756603750785)
      ·
        refine ⟨4427641532297067452813089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5903522043062756603750785 4427641532297067452813089)
        ·
          refine ⟨3320731149222800589609817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4427641532297067452813089 3320731149222800589609817)
          ·
            refine ⟨2490548361917100442207363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3320731149222800589609817 2490548361917100442207363)
            ·
              refine ⟨3735822542875650663311045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2490548361917100442207363 3735822542875650663311045)
              ·
                refine ⟨700466726789184499370821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3735822542875650663311045 700466726789184499370821)
                ·
                  refine ⟨131337511272972093632029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 700466726789184499370821 131337511272972093632029)
                  ·
                    rfl

theorem cell22_1151005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_1151005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151005 prefixEnd_1151005 := by exact prefixLift 1151005
  have htrace : WordTrace (prefixWord ++ tailWord_1151005) baseStart_1151005 baseEnd_1151005 := by
    simpa [prefixWord, tailWord_1151005, baseEnd_1151005] using wordTrace_append hprefix tailTrace_1151005
  have hstable : (prefixWord ++ tailWord_1151005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151005).length < 2 ^ (prefixWord ++ tailWord_1151005).sum := by decide
  have hdescent : baseEnd_1151005 < baseStart_1151005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151065 : List Nat := [1, 2, 1, 2, 2, 1, 3, 6, 1, 3]
def baseStart_1151065 : Nat := 118140960795 + 1151065 * 2 ^ 59
def prefixEnd_1151065 : Nat := 4983230072969 + 3 ^ 40 * 1151065 * 2
def baseEnd_1151065 : Nat := 394033073045096124395903

theorem tailTrace_1151065 : CollatzResearch.WordTrace tailWord_1151065 prefixEnd_1151065 394033073045096124395903 := by
  unfold tailWord_1151065
  simp only [CollatzResearch.WordTrace]
  refine ⟨41982789574895566096078649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27988526383263710730719099 41982789574895566096078649)
  ·
    refine ⟨31487092181171674572058987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41982789574895566096078649 31487092181171674572058987)
    ·
      refine ⟨47230638271757511858088481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31487092181171674572058987 47230638271757511858088481)
      ·
        refine ⟨35422978703818133893566361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47230638271757511858088481 35422978703818133893566361)
        ·
          refine ⟨26567234027863600420174771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35422978703818133893566361 26567234027863600420174771)
          ·
            refine ⟨39850851041795400630262157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26567234027863600420174771 39850851041795400630262157)
            ·
              refine ⟨14944069140673275236348309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39850851041795400630262157 14944069140673275236348309)
              ·
                refine ⟨700503240969059776703827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14944069140673275236348309 700503240969059776703827)
                ·
                  refine ⟨1050754861453589665055741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700503240969059776703827 1050754861453589665055741)
                  ·
                    refine ⟨394033073045096124395903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1050754861453589665055741 394033073045096124395903)
                    ·
                      rfl

theorem cell22_1151065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 1, 3].length) (baseStart_1151065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151065 prefixEnd_1151065 := by exact prefixLift 1151065
  have htrace : WordTrace (prefixWord ++ tailWord_1151065) baseStart_1151065 baseEnd_1151065 := by
    simpa [prefixWord, tailWord_1151065, baseEnd_1151065] using wordTrace_append hprefix tailTrace_1151065
  have hstable : (prefixWord ++ tailWord_1151065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151065).length < 2 ^ (prefixWord ++ tailWord_1151065).sum := by decide
  have hdescent : baseEnd_1151065 < baseStart_1151065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151172 : List Nat := [2, 3, 3, 1, 2, 1, 1, 4, 2, 3]
def baseStart_1151172 : Nat := 118140960795 + 1151172 * 2 ^ 59
def prefixEnd_1151172 : Nat := 4983230072969 + 3 ^ 40 * 1151172 * 2
def baseEnd_1151172 : Nat := 394069701331783511970575

theorem tailTrace_1151172 : CollatzResearch.WordTrace tailWord_1151172 prefixEnd_1151172 394069701331783511970575 := by
  unfold tailWord_1151172
  simp only [CollatzResearch.WordTrace]
  refine ⟨20993346092753961685111885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27991128123671948913482513 20993346092753961685111885)
  ·
    refine ⟨7872504784782735631916957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20993346092753961685111885 7872504784782735631916957)
    ·
      refine ⟨2952189294293525861968859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7872504784782735631916957 2952189294293525861968859)
      ·
        refine ⟨4428283941440288792953289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2952189294293525861968859 4428283941440288792953289)
        ·
          refine ⟨3321212956080216594714967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4428283941440288792953289 3321212956080216594714967)
          ·
            refine ⟨4981819434120324892072451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3321212956080216594714967 4981819434120324892072451)
            ·
              refine ⟨7472729151180487338108677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4981819434120324892072451 7472729151180487338108677)
              ·
                refine ⟨1401136715846341375895377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7472729151180487338108677 1401136715846341375895377)
                ·
                  refine ⟨1050852536884756031921533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1401136715846341375895377 1050852536884756031921533)
                  ·
                    refine ⟨394069701331783511970575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1050852536884756031921533 394069701331783511970575)
                    ·
                      rfl

theorem cell22_1151172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_1151172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151172 prefixEnd_1151172 := by exact prefixLift 1151172
  have htrace : WordTrace (prefixWord ++ tailWord_1151172) baseStart_1151172 baseEnd_1151172 := by
    simpa [prefixWord, tailWord_1151172, baseEnd_1151172] using wordTrace_append hprefix tailTrace_1151172
  have hstable : (prefixWord ++ tailWord_1151172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151172).length < 2 ^ (prefixWord ++ tailWord_1151172).sum := by decide
  have hdescent : baseEnd_1151172 < baseStart_1151172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151200 : List Nat := [2, 1, 1, 3, 1, 3, 3, 2, 3, 3]
def baseStart_1151200 : Nat := 118140960795 + 1151200 * 2 ^ 59
def prefixEnd_1151200 : Nat := 4983230072969 + 3 ^ 40 * 1151200 * 2
def baseEnd_1151200 : Nat := 394079286304000772270489

theorem tailTrace_1151200 : CollatzResearch.WordTrace tailWord_1151200 prefixEnd_1151200 394079286304000772270489 := by
  unfold tailWord_1151200
  simp only [CollatzResearch.WordTrace]
  refine ⟨20993856714703242076121527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27991808952937656101495369 20993856714703242076121527)
  ·
    refine ⟨31490785072054863114182291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20993856714703242076121527 31490785072054863114182291)
    ·
      refine ⟨47236177608082294671273437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31490785072054863114182291 47236177608082294671273437)
      ·
        refine ⟨17713566603030860501727539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47236177608082294671273437 17713566603030860501727539)
        ·
          refine ⟨26570349904546290752591309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17713566603030860501727539 26570349904546290752591309)
          ·
            refine ⟨9963881214204859032221741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26570349904546290752591309 9963881214204859032221741)
            ·
              refine ⟨3736455455326822137083153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9963881214204859032221741 3736455455326822137083153)
              ·
                refine ⟨2802341591495116602812365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3736455455326822137083153 2802341591495116602812365)
                ·
                  refine ⟨1050878096810668726054637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2802341591495116602812365 1050878096810668726054637)
                  ·
                    refine ⟨394079286304000772270489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1050878096810668726054637 394079286304000772270489)
                    ·
                      rfl

theorem cell22_1151200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 3, 3].length) (baseStart_1151200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151200 prefixEnd_1151200 := by exact prefixLift 1151200
  have htrace : WordTrace (prefixWord ++ tailWord_1151200) baseStart_1151200 baseEnd_1151200 := by
    simpa [prefixWord, tailWord_1151200, baseEnd_1151200] using wordTrace_append hprefix tailTrace_1151200
  have hstable : (prefixWord ++ tailWord_1151200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151200).length < 2 ^ (prefixWord ++ tailWord_1151200).sum := by decide
  have hdescent : baseEnd_1151200 < baseStart_1151200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151217 : List Nat := [1, 2, 2, 2, 2, 1, 3, 5, 1, 3]
def baseStart_1151217 : Nat := 118140960795 + 1151217 * 2 ^ 59
def prefixEnd_1151217 : Nat := 4983230072969 + 3 ^ 40 * 1151217 * 2
def baseEnd_1151217 : Nat := 394085105751418394595437

theorem tailTrace_1151217 : CollatzResearch.WordTrace tailWord_1151217 prefixEnd_1151217 394085105751418394595437 := by
  unfold tailWord_1151217
  simp only [CollatzResearch.WordTrace]
  refine ⟨41988333470344896055611905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27992222313563264037074603 41988333470344896055611905)
  ·
    refine ⟨31491250102758672041708929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41988333470344896055611905 31491250102758672041708929)
    ·
      refine ⟨23618437577069004031281697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31491250102758672041708929 23618437577069004031281697)
      ·
        refine ⟨17713828182801753023461273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23618437577069004031281697 17713828182801753023461273)
        ·
          refine ⟨13285371137101314767595955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17713828182801753023461273 13285371137101314767595955)
          ·
            refine ⟨19928056705651972151393933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13285371137101314767595955 19928056705651972151393933)
            ·
              refine ⟨7473021264619489556772725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19928056705651972151393933 7473021264619489556772725)
              ·
                refine ⟨700595743558077145947443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7473021264619489556772725 700595743558077145947443)
                ·
                  refine ⟨1050893615337115718921165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700595743558077145947443 1050893615337115718921165)
                  ·
                    refine ⟨394085105751418394595437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1050893615337115718921165 394085105751418394595437)
                    ·
                      rfl

theorem cell22_1151217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 1, 3].length) (baseStart_1151217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151217 prefixEnd_1151217 := by exact prefixLift 1151217
  have htrace : WordTrace (prefixWord ++ tailWord_1151217) baseStart_1151217 baseEnd_1151217 := by
    simpa [prefixWord, tailWord_1151217, baseEnd_1151217] using wordTrace_append hprefix tailTrace_1151217
  have hstable : (prefixWord ++ tailWord_1151217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151217).length < 2 ^ (prefixWord ++ tailWord_1151217).sum := by decide
  have hdescent : baseEnd_1151217 < baseStart_1151217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151230 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 7]
def baseStart_1151230 : Nat := 118140960795 + 1151230 * 2 ^ 59
def prefixEnd_1151230 : Nat := 4983230072969 + 3 ^ 40 * 1151230 * 2
def baseEnd_1151230 : Nat := 131363185305696898006799

theorem tailTrace_1151230 : CollatzResearch.WordTrace tailWord_1151230 prefixEnd_1151230 131363185305696898006799 := by
  unfold tailWord_1151230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5248600952412224909479393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27992538412865199517223429 5248600952412224909479393)
  ·
    refine ⟨3936450714309168682109545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5248600952412224909479393 3936450714309168682109545)
    ·
      refine ⟨2952338035731876511582159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3936450714309168682109545 2952338035731876511582159)
      ·
        refine ⟨4428507053597814767373239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2952338035731876511582159 4428507053597814767373239)
        ·
          refine ⟨6642760580396722151059859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4428507053597814767373239 6642760580396722151059859)
          ·
            refine ⟨9964140870595083226589789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6642760580396722151059859 9964140870595083226589789)
            ·
              refine ⟨3736552826473156209971171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9964140870595083226589789 3736552826473156209971171)
              ·
                refine ⟨5604829239709734314956757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3736552826473156209971171 5604829239709734314956757)
                ·
                  refine ⟨131363185305696898006799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5604829239709734314956757 131363185305696898006799)
                  ·
                    rfl

theorem cell22_1151230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_1151230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151230 prefixEnd_1151230 := by exact prefixLift 1151230
  have htrace : WordTrace (prefixWord ++ tailWord_1151230) baseStart_1151230 baseEnd_1151230 := by
    simpa [prefixWord, tailWord_1151230, baseEnd_1151230] using wordTrace_append hprefix tailTrace_1151230
  have hstable : (prefixWord ++ tailWord_1151230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151230).length < 2 ^ (prefixWord ++ tailWord_1151230).sum := by decide
  have hdescent : baseEnd_1151230 < baseStart_1151230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151234 : List Nat := [3, 4, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_1151234 : Nat := 118140960795 + 1151234 * 2 ^ 59
def prefixEnd_1151234 : Nat := 4983230072969 + 3 ^ 40 * 1151234 * 2
def baseEnd_1151234 : Nat := 394090925198836016920385

theorem tailTrace_1151234 : CollatzResearch.WordTrace tailWord_1151234 prefixEnd_1151234 394090925198836016920385 := by
  unfold tailWord_1151234
  simp only [CollatzResearch.WordTrace]
  refine ⟨10497238377820826989745189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27992635674188871972653837 10497238377820826989745189)
  ·
    refine ⟨1968232195841405060577223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10497238377820826989745189 1968232195841405060577223)
    ·
      refine ⟨2952348293762107590865835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1968232195841405060577223 2952348293762107590865835)
      ·
        refine ⟨4428522440643161386298753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2952348293762107590865835 4428522440643161386298753)
        ·
          refine ⟨3321391830482371039724065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4428522440643161386298753 3321391830482371039724065)
          ·
            refine ⟨2491043872861778279793049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3321391830482371039724065 2491043872861778279793049)
            ·
              refine ⟨1868282904646333709844787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2491043872861778279793049 1868282904646333709844787)
              ·
                refine ⟨2802424356969500564767181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1868282904646333709844787 2802424356969500564767181)
                ·
                  refine ⟨1050909133863562711787693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2802424356969500564767181 1050909133863562711787693)
                  ·
                    refine ⟨394090925198836016920385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1050909133863562711787693 394090925198836016920385)
                    ·
                      rfl

theorem cell22_1151234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_1151234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151234 prefixEnd_1151234 := by exact prefixLift 1151234
  have htrace : WordTrace (prefixWord ++ tailWord_1151234) baseStart_1151234 baseEnd_1151234 := by
    simpa [prefixWord, tailWord_1151234, baseEnd_1151234] using wordTrace_append hprefix tailTrace_1151234
  have hstable : (prefixWord ++ tailWord_1151234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151234).length < 2 ^ (prefixWord ++ tailWord_1151234).sum := by decide
  have hdescent : baseEnd_1151234 < baseStart_1151234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151324 : List Nat := [2, 2, 4, 3, 1, 1, 1, 2, 1, 5]
def baseStart_1151324 : Nat := 118140960795 + 1151324 * 2 ^ 59
def prefixEnd_1151324 : Nat := 4983230072969 + 3 ^ 40 * 1151324 * 2
def baseEnd_1151324 : Nat := 394121734038105782170109

theorem tailTrace_1151324 : CollatzResearch.WordTrace tailWord_1151324 prefixEnd_1151324 394121734038105782170109 := by
  unfold tailWord_1151324
  simp only [CollatzResearch.WordTrace]
  refine ⟨20996118040478626664878513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27994824053971502219838017 20996118040478626664878513)
  ·
    refine ⟨15747088530358969998658885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20996118040478626664878513 15747088530358969998658885)
    ·
      refine ⟨2952579099442306874748541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15747088530358969998658885 2952579099442306874748541)
      ·
        refine ⟨1107217162290865078030703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2952579099442306874748541 1107217162290865078030703)
        ·
          refine ⟨1660825743436297617046055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107217162290865078030703 1660825743436297617046055)
          ·
            refine ⟨2491238615154446425569083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1660825743436297617046055 2491238615154446425569083)
            ·
              refine ⟨3736857922731669638353625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2491238615154446425569083 3736857922731669638353625)
              ·
                refine ⟨2802643442048752228765219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3736857922731669638353625 2802643442048752228765219)
                ·
                  refine ⟨4203965163073128343147829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2802643442048752228765219 4203965163073128343147829)
                  ·
                    refine ⟨394121734038105782170109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4203965163073128343147829 394121734038105782170109)
                    ·
                      rfl

theorem cell22_1151324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_1151324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151324 prefixEnd_1151324 := by exact prefixLift 1151324
  have htrace : WordTrace (prefixWord ++ tailWord_1151324) baseStart_1151324 baseEnd_1151324 := by
    simpa [prefixWord, tailWord_1151324, baseEnd_1151324] using wordTrace_append hprefix tailTrace_1151324
  have hstable : (prefixWord ++ tailWord_1151324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151324).length < 2 ^ (prefixWord ++ tailWord_1151324).sum := by decide
  have hdescent : baseEnd_1151324 < baseStart_1151324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151386 : List Nat := [3, 1, 1, 4, 1, 3, 2, 3, 1, 3]
def baseStart_1151386 : Nat := 118140960795 + 1151386 * 2 ^ 59
def prefixEnd_1151386 : Nat := 4983230072969 + 3 ^ 40 * 1151386 * 2
def baseEnd_1151386 : Nat := 394142957905158287119919

theorem tailTrace_1151386 : CollatzResearch.WordTrace tailWord_1151386 prefixEnd_1151386 394142957905158287119919 := by
  unfold tailWord_1151386
  simp only [CollatzResearch.WordTrace]
  refine ⟨10498624351683159479628503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27996331604488425279009341 10498624351683159479628503)
  ·
    refine ⟨15747936527524739219442755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10498624351683159479628503 15747936527524739219442755)
    ·
      refine ⟨23621904791287108829164133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15747936527524739219442755 23621904791287108829164133)
      ·
        refine ⟨4429107148366332905468275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23621904791287108829164133 4429107148366332905468275)
        ·
          refine ⟨6643660722549499358202413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4429107148366332905468275 6643660722549499358202413)
          ·
            refine ⟨2491372770956062259325905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6643660722549499358202413 2491372770956062259325905)
            ·
              refine ⟨1868529578217046694494429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2491372770956062259325905 1868529578217046694494429)
              ·
                refine ⟨700698591831392510435411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1868529578217046694494429 700698591831392510435411)
                ·
                  refine ⟨1051047887747088765653117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700698591831392510435411 1051047887747088765653117)
                  ·
                    refine ⟨394142957905158287119919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1051047887747088765653117 394142957905158287119919)
                    ·
                      rfl

theorem cell22_1151386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 1, 3].length) (baseStart_1151386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151386 prefixEnd_1151386 := by exact prefixLift 1151386
  have htrace : WordTrace (prefixWord ++ tailWord_1151386) baseStart_1151386 baseEnd_1151386 := by
    simpa [prefixWord, tailWord_1151386, baseEnd_1151386] using wordTrace_append hprefix tailTrace_1151386
  have hstable : (prefixWord ++ tailWord_1151386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151386).length < 2 ^ (prefixWord ++ tailWord_1151386).sum := by decide
  have hdescent : baseEnd_1151386 < baseStart_1151386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151399 : List Nat := [1, 1, 6, 1, 1, 4, 1, 2, 5]
def baseStart_1151399 : Nat := 118140960795 + 1151399 * 2 ^ 59
def prefixEnd_1151399 : Nat := 4983230072969 + 3 ^ 40 * 1151399 * 2
def baseEnd_1151399 : Nat := 131382469356943528848293

theorem tailTrace_1151399 : CollatzResearch.WordTrace tailWord_1151399 prefixEnd_1151399 131382469356943528848293 := by
  unfold tailWord_1151399
  simp only [CollatzResearch.WordTrace]
  refine ⟨41994971555685541138737251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27996647703790360759158167 41994971555685541138737251)
  ·
    refine ⟨62992457333528311708105877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41994971555685541138737251 62992457333528311708105877)
    ·
      refine ⟨2952771437509139611317463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 62992457333528311708105877 2952771437509139611317463)
      ·
        refine ⟨4429157156263709416976195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2952771437509139611317463 4429157156263709416976195)
        ·
          refine ⟨6643735734395564125464293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4429157156263709416976195 6643735734395564125464293)
          ·
            refine ⟨1245700450199168273524555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6643735734395564125464293 1245700450199168273524555)
            ·
              refine ⟨1868550675298752410286833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1245700450199168273524555 1868550675298752410286833)
              ·
                refine ⟨1401413006474064307715125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1868550675298752410286833 1401413006474064307715125)
                ·
                  refine ⟨131382469356943528848293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1401413006474064307715125 131382469356943528848293)
                  ·
                    rfl

theorem cell22_1151399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 5].length) (baseStart_1151399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151399 prefixEnd_1151399 := by exact prefixLift 1151399
  have htrace : WordTrace (prefixWord ++ tailWord_1151399) baseStart_1151399 baseEnd_1151399 := by
    simpa [prefixWord, tailWord_1151399, baseEnd_1151399] using wordTrace_append hprefix tailTrace_1151399
  have hstable : (prefixWord ++ tailWord_1151399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151399).length < 2 ^ (prefixWord ++ tailWord_1151399).sum := by decide
  have hdescent : baseEnd_1151399 < baseStart_1151399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151455 : List Nat := [1, 1, 2, 3, 3, 2, 10]
def baseStart_1151455 : Nat := 118140960795 + 1151455 * 2 ^ 59
def prefixEnd_1151455 : Nat := 4983230072969 + 3 ^ 40 * 1151455 * 2
def baseEnd_1151455 : Nat := 14598762148713522486841

theorem tailTrace_1151455 : CollatzResearch.WordTrace tailWord_1151455 prefixEnd_1151455 14598762148713522486841 := by
  unfold tailWord_1151455
  simp only [CollatzResearch.WordTrace]
  refine ⟨41997014043482662702775819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27998009362321775135183879 41997014043482662702775819)
  ·
    refine ⟨62995521065223994054163729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41997014043482662702775819 62995521065223994054163729)
    ·
      refine ⟨47246640798917995540622797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62995521065223994054163729 47246640798917995540622797)
      ·
        refine ⟨17717490299594248327733549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47246640798917995540622797 17717490299594248327733549)
        ·
          refine ⟨6644058862347843122900081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17717490299594248327733549 6644058862347843122900081)
          ·
            refine ⟨4983044146760882342175061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6644058862347843122900081 4983044146760882342175061)
            ·
              refine ⟨14598762148713522486841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4983044146760882342175061 14598762148713522486841)
              ·
                rfl

theorem cell22_1151455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 10].length) (baseStart_1151455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151455 prefixEnd_1151455 := by exact prefixLift 1151455
  have htrace : WordTrace (prefixWord ++ tailWord_1151455) baseStart_1151455 baseEnd_1151455 := by
    simpa [prefixWord, tailWord_1151455, baseEnd_1151455] using wordTrace_append hprefix tailTrace_1151455
  have hstable : (prefixWord ++ tailWord_1151455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151455).length < 2 ^ (prefixWord ++ tailWord_1151455).sum := by decide
  have hdescent : baseEnd_1151455 < baseStart_1151455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151457 : List Nat := [1, 2, 3, 1, 2, 2, 3, 2, 2, 4]
def baseStart_1151457 : Nat := 118140960795 + 1151457 * 2 ^ 59
def prefixEnd_1151457 : Nat := 4983230072969 + 3 ^ 40 * 1151457 * 2
def baseEnd_1151457 : Nat := 394167262656137768594701

theorem tailTrace_1151457 : CollatzResearch.WordTrace tailWord_1151457 prefixEnd_1151457 394167262656137768594701 := by
  unfold tailWord_1151457
  simp only [CollatzResearch.WordTrace]
  refine ⟨41997086989475417044348625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27998057992983611362899083 41997086989475417044348625)
  ·
    refine ⟨31497815242106562783261469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41997086989475417044348625 31497815242106562783261469)
    ·
      refine ⟨11811680715789961043723051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31497815242106562783261469 11811680715789961043723051)
      ·
        refine ⟨17717521073684941565584577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11811680715789961043723051 17717521073684941565584577)
        ·
          refine ⟨13288140805263706174188433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17717521073684941565584577 13288140805263706174188433)
          ·
            refine ⟨9966105603947779630641325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13288140805263706174188433 9966105603947779630641325)
            ·
              refine ⟨3737289601480417361490497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9966105603947779630641325 3737289601480417361490497)
              ·
                refine ⟨2802967201110313021117873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3737289601480417361490497 2802967201110313021117873)
                ·
                  refine ⟨2102225400832734765838405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2802967201110313021117873 2102225400832734765838405)
                  ·
                    refine ⟨394167262656137768594701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2102225400832734765838405 394167262656137768594701)
                    ·
                      rfl

theorem cell22_1151457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_1151457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151457 prefixEnd_1151457 := by exact prefixLift 1151457
  have htrace : WordTrace (prefixWord ++ tailWord_1151457) baseStart_1151457 baseEnd_1151457 := by
    simpa [prefixWord, tailWord_1151457, baseEnd_1151457] using wordTrace_append hprefix tailTrace_1151457
  have hstable : (prefixWord ++ tailWord_1151457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151457).length < 2 ^ (prefixWord ++ tailWord_1151457).sum := by decide
  have hdescent : baseEnd_1151457 < baseStart_1151457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151461 : List Nat := [1, 3, 1, 5, 3, 1, 1, 1, 6]
def baseStart_1151461 : Nat := 118140960795 + 1151461 * 2 ^ 59
def prefixEnd_1151461 : Nat := 4983230072969 + 3 ^ 40 * 1151461 * 2
def baseEnd_1151461 : Nat := 131389543979294363831563

theorem tailTrace_1151461 : CollatzResearch.WordTrace tailWord_1151461 prefixEnd_1151461 131389543979294363831563 := by
  unfold tailWord_1151461
  simp only [CollatzResearch.WordTrace]
  refine ⟨41997232881460925727494237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27998155254307283818329491 41997232881460925727494237)
  ·
    refine ⟨15748962330547847147810339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41997232881460925727494237 15748962330547847147810339)
    ·
      refine ⟨23623443495821770721715509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15748962330547847147810339 23623443495821770721715509)
      ·
        refine ⟨2214697827733291005160829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23623443495821770721715509 2214697827733291005160829)
        ·
          refine ⟨830511685399984126935311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2214697827733291005160829 830511685399984126935311)
          ·
            refine ⟨1245767528099976190402967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830511685399984126935311 1245767528099976190402967)
            ·
              refine ⟨1868651292149964285604451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1245767528099976190402967 1868651292149964285604451)
              ·
                refine ⟨2802976938224946428406677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1868651292149964285604451 2802976938224946428406677)
                ·
                  refine ⟨131389543979294363831563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2802976938224946428406677 131389543979294363831563)
                  ·
                    rfl

theorem cell22_1151461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 6].length) (baseStart_1151461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151461 prefixEnd_1151461 := by exact prefixLift 1151461
  have htrace : WordTrace (prefixWord ++ tailWord_1151461) baseStart_1151461 baseEnd_1151461 := by
    simpa [prefixWord, tailWord_1151461, baseEnd_1151461] using wordTrace_append hprefix tailTrace_1151461
  have hstable : (prefixWord ++ tailWord_1151461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151461).length < 2 ^ (prefixWord ++ tailWord_1151461).sum := by decide
  have hdescent : baseEnd_1151461 < baseStart_1151461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151487 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 5, 3]
def baseStart_1151487 : Nat := 118140960795 + 1151487 * 2 ^ 59
def prefixEnd_1151487 : Nat := 4983230072969 + 3 ^ 40 * 1151487 * 2
def baseEnd_1151487 : Nat := 394177532269227690344609

theorem tailTrace_1151487 : CollatzResearch.WordTrace tailWord_1151487 prefixEnd_1151487 394177532269227690344609 := by
  unfold tailWord_1151487
  simp only [CollatzResearch.WordTrace]
  refine ⟨41998181179366732167940715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27998787452911154778627143 41998181179366732167940715)
  ·
    refine ⟨62997271769050098251911073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41998181179366732167940715 62997271769050098251911073)
    ·
      refine ⟨47247953826787573688933305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62997271769050098251911073 47247953826787573688933305)
      ·
        refine ⟨35435965370090680266699979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47247953826787573688933305 35435965370090680266699979)
        ·
          refine ⟨53153948055136020400049969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35435965370090680266699979 53153948055136020400049969)
          ·
            refine ⟨39865461041352015300037477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53153948055136020400049969 39865461041352015300037477)
            ·
              refine ⟨7474773945253502868757027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39865461041352015300037477 7474773945253502868757027)
              ·
                refine ⟨11212160917880254303135541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7474773945253502868757027 11212160917880254303135541)
                ·
                  refine ⟨1051140086051273840918957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11212160917880254303135541 1051140086051273840918957)
                  ·
                    refine ⟨394177532269227690344609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1051140086051273840918957 394177532269227690344609)
                    ·
                      rfl

theorem cell22_1151487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 3].length) (baseStart_1151487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151487 prefixEnd_1151487 := by exact prefixLift 1151487
  have htrace : WordTrace (prefixWord ++ tailWord_1151487) baseStart_1151487 baseEnd_1151487 := by
    simpa [prefixWord, tailWord_1151487, baseEnd_1151487] using wordTrace_append hprefix tailTrace_1151487
  have hstable : (prefixWord ++ tailWord_1151487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151487).length < 2 ^ (prefixWord ++ tailWord_1151487).sum := by decide
  have hdescent : baseEnd_1151487 < baseStart_1151487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151515 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 5, 7]
def baseStart_1151515 : Nat := 118140960795 + 1151515 * 2 ^ 59
def prefixEnd_1151515 : Nat := 4983230072969 + 3 ^ 40 * 1151515 * 2
def baseEnd_1151515 : Nat := 394187117241444950644523

theorem tailTrace_1151515 : CollatzResearch.WordTrace tailWord_1151515 prefixEnd_1151515 394187117241444950644523 := by
  unfold tailWord_1151515
  simp only [CollatzResearch.WordTrace]
  refine ⟨41999202423265292949959999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27999468282176861966639999 41999202423265292949959999)
  ·
    refine ⟨62998803634897939424939999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41999202423265292949959999 62998803634897939424939999)
    ·
      refine ⟨94498205452346909137409999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62998803634897939424939999 94498205452346909137409999)
      ·
        refine ⟨141747308178520363706114999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94498205452346909137409999 141747308178520363706114999)
        ·
          refine ⟨212620962267780545559172499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141747308178520363706114999 212620962267780545559172499)
          ·
            refine ⟨318931443401670818338758749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212620962267780545559172499 318931443401670818338758749)
            ·
              refine ⟨119599291275626556877034531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 318931443401670818338758749 119599291275626556877034531)
              ·
                refine ⟨179398936913439835315551797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119599291275626556877034531 179398936913439835315551797)
                ·
                  refine ⟨16818650335634984560832981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 179398936913439835315551797 16818650335634984560832981)
                  ·
                    refine ⟨394187117241444950644523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16818650335634984560832981 394187117241444950644523)
                    ·
                      rfl

theorem cell22_1151515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 7].length) (baseStart_1151515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151515 prefixEnd_1151515 := by exact prefixLift 1151515
  have htrace : WordTrace (prefixWord ++ tailWord_1151515) baseStart_1151515 baseEnd_1151515 := by
    simpa [prefixWord, tailWord_1151515, baseEnd_1151515] using wordTrace_append hprefix tailTrace_1151515
  have hstable : (prefixWord ++ tailWord_1151515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151515).length < 2 ^ (prefixWord ++ tailWord_1151515).sum := by decide
  have hdescent : baseEnd_1151515 < baseStart_1151515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151521 : List Nat := [1, 2, 3, 2, 2, 1, 3, 4, 1, 3]
def baseStart_1151521 : Nat := 118140960795 + 1151521 * 2 ^ 59
def prefixEnd_1151521 : Nat := 4983230072969 + 3 ^ 40 * 1151521 * 2
def baseEnd_1151521 : Nat := 394189171164062934994505

theorem tailTrace_1151521 : CollatzResearch.WordTrace tailWord_1151521 prefixEnd_1151521 394189171164062934994505 := by
  unfold tailWord_1151521
  simp only [CollatzResearch.WordTrace]
  refine ⟨41999421261243555974678417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27999614174162370649785611 41999421261243555974678417)
  ·
    refine ⟨31499565945932666981008813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41999421261243555974678417 31499565945932666981008813)
    ·
      refine ⟨11812337229724750117878305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31499565945932666981008813 11812337229724750117878305)
      ·
        refine ⟨8859252922293562588408729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11812337229724750117878305 8859252922293562588408729)
        ·
          refine ⟨6644439691720171941306547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8859252922293562588408729 6644439691720171941306547)
          ·
            refine ⟨9966659537580257911959821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6644439691720171941306547 9966659537580257911959821)
            ·
              refine ⟨3737497326592596716984933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9966659537580257911959821 3737497326592596716984933)
              ·
                refine ⟨700780748736111884434675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3737497326592596716984933 700780748736111884434675)
                ·
                  refine ⟨1051171123104167826652013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700780748736111884434675 1051171123104167826652013)
                  ·
                    refine ⟨394189171164062934994505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1051171123104167826652013 394189171164062934994505)
                    ·
                      rfl

theorem cell22_1151521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_1151521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151521 prefixEnd_1151521 := by exact prefixLift 1151521
  have htrace : WordTrace (prefixWord ++ tailWord_1151521) baseStart_1151521 baseEnd_1151521 := by
    simpa [prefixWord, tailWord_1151521, baseEnd_1151521] using wordTrace_append hprefix tailTrace_1151521
  have hstable : (prefixWord ++ tailWord_1151521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151521).length < 2 ^ (prefixWord ++ tailWord_1151521).sum := by decide
  have hdescent : baseEnd_1151521 < baseStart_1151521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151564 : List Nat := [2, 2, 1, 3, 1, 2, 3, 3, 1, 4]
def baseStart_1151564 : Nat := 118140960795 + 1151564 * 2 ^ 59
def prefixEnd_1151564 : Nat := 4983230072969 + 3 ^ 40 * 1151564 * 2
def baseEnd_1151564 : Nat := 394203890942825156169373

theorem tailTrace_1151564 : CollatzResearch.WordTrace tailWord_1151564 prefixEnd_1151564 394203890942825156169373 := by
  unfold tailWord_1151564
  simp only [CollatzResearch.WordTrace]
  refine ⟨21000494800043887159246873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28000659733391849545662497 21000494800043887159246873)
  ·
    refine ⟨15750371100032915369435155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21000494800043887159246873 15750371100032915369435155)
    ·
      refine ⟨23625556650049373054152733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15750371100032915369435155 23625556650049373054152733)
      ·
        refine ⟨8859583743768514895307275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23625556650049373054152733 8859583743768514895307275)
        ·
          refine ⟨13289375615652772342960913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8859583743768514895307275 13289375615652772342960913)
          ·
            refine ⟨9967031711739579257220685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13289375615652772342960913 9967031711739579257220685)
            ·
              refine ⟨3737636891902342221457757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9967031711739579257220685 3737636891902342221457757)
              ·
                refine ⟨1401613834463378333046659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3737636891902342221457757 1401613834463378333046659)
                ·
                  refine ⟨2102420751695067499569989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1401613834463378333046659 2102420751695067499569989)
                  ·
                    refine ⟨394203890942825156169373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2102420751695067499569989 394203890942825156169373)
                    ·
                      rfl

theorem cell22_1151564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_1151564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151564 prefixEnd_1151564 := by exact prefixLift 1151564
  have htrace : WordTrace (prefixWord ++ tailWord_1151564) baseStart_1151564 baseEnd_1151564 := by
    simpa [prefixWord, tailWord_1151564, baseEnd_1151564] using wordTrace_append hprefix tailTrace_1151564
  have hstable : (prefixWord ++ tailWord_1151564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151564).length < 2 ^ (prefixWord ++ tailWord_1151564).sum := by decide
  have hdescent : baseEnd_1151564 < baseStart_1151564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151613 : List Nat := [1, 4, 1, 1, 5, 2, 1, 3, 4]
def baseStart_1151613 : Nat := 118140960795 + 1151613 * 2 ^ 59
def prefixEnd_1151613 : Nat := 4983230072969 + 3 ^ 40 * 1151613 * 2
def baseEnd_1151613 : Nat := 131406888214735120564741

theorem tailTrace_1151613 : CollatzResearch.WordTrace tailWord_1151613 prefixEnd_1151613 131406888214735120564741 := by
  unfold tailWord_1151613
  simp only [CollatzResearch.WordTrace]
  refine ⟨42002776776910255687027493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28001851184606837124684995 42002776776910255687027493)
  ·
    refine ⟨7875520645670672941317655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42002776776910255687027493 7875520645670672941317655)
    ·
      refine ⟨11813280968506009411976483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7875520645670672941317655 11813280968506009411976483)
      ·
        refine ⟨17719921452759014117964725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11813280968506009411976483 17719921452759014117964725)
        ·
          refine ⟨1661242636196157573559193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17719921452759014117964725 1661242636196157573559193)
          ·
            refine ⟨1245931977147118180169395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1661242636196157573559193 1245931977147118180169395)
            ·
              refine ⟨1868897965720677270254093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1245931977147118180169395 1868897965720677270254093)
              ·
                refine ⟨700836737145253976345285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1868897965720677270254093 700836737145253976345285)
                ·
                  refine ⟨131406888214735120564741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 700836737145253976345285 131406888214735120564741)
                  ·
                    rfl

theorem cell22_1151613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_1151613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151613 prefixEnd_1151613 := by exact prefixLift 1151613
  have htrace : WordTrace (prefixWord ++ tailWord_1151613) baseStart_1151613 baseEnd_1151613 := by
    simpa [prefixWord, tailWord_1151613, baseEnd_1151613] using wordTrace_append hprefix tailTrace_1151613
  have hstable : (prefixWord ++ tailWord_1151613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151613).length < 2 ^ (prefixWord ++ tailWord_1151613).sum := by decide
  have hdescent : baseEnd_1151613 < baseStart_1151613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151626 : List Nat := [3, 1, 2, 3, 3, 1, 1, 2, 2, 4]
def baseStart_1151626 : Nat := 118140960795 + 1151626 * 2 ^ 59
def prefixEnd_1151626 : Nat := 4983230072969 + 3 ^ 40 * 1151626 * 2
def baseEnd_1151626 : Nat := 394225114809877661119183

theorem tailTrace_1151626 : CollatzResearch.WordTrace tailWord_1151626 prefixEnd_1151626 394225114809877661119183 := by
  unfold tailWord_1151626
  simp only [CollatzResearch.WordTrace]
  refine ⟨10500812731465789726812683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28002167283908772604833821 10500812731465789726812683)
  ·
    refine ⟨15751219097198684590219025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10500812731465789726812683 15751219097198684590219025)
    ·
      refine ⟨11813414322899013442664269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15751219097198684590219025 11813414322899013442664269)
      ·
        refine ⟨4430030371087130040999101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11813414322899013442664269 4430030371087130040999101)
        ·
          refine ⟨1661261389157673765374663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4430030371087130040999101 1661261389157673765374663)
          ·
            refine ⟨2491892083736510648061995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1661261389157673765374663 2491892083736510648061995)
            ·
              refine ⟨3737838125604765972092993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2491892083736510648061995 3737838125604765972092993)
              ·
                refine ⟨2803378594203574479069745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3737838125604765972092993 2803378594203574479069745)
                ·
                  refine ⟨2102533945652680859302309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2803378594203574479069745 2102533945652680859302309)
                  ·
                    refine ⟨394225114809877661119183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2102533945652680859302309 394225114809877661119183)
                    ·
                      rfl

theorem cell22_1151626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_1151626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151626 prefixEnd_1151626 := by exact prefixLift 1151626
  have htrace : WordTrace (prefixWord ++ tailWord_1151626) baseStart_1151626 baseEnd_1151626 := by
    simpa [prefixWord, tailWord_1151626, baseEnd_1151626] using wordTrace_append hprefix tailTrace_1151626
  have hstable : (prefixWord ++ tailWord_1151626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151626).length < 2 ^ (prefixWord ++ tailWord_1151626).sum := by decide
  have hdescent : baseEnd_1151626 < baseStart_1151626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151690 : List Nat := [3, 1, 2, 1, 4, 1, 4, 2, 1, 3]
def baseStart_1151690 : Nat := 118140960795 + 1151690 * 2 ^ 59
def prefixEnd_1151690 : Nat := 4983230072969 + 3 ^ 40 * 1151690 * 2
def baseEnd_1151690 : Nat := 394247023317802827518987

theorem tailTrace_1151690 : CollatzResearch.WordTrace tailWord_1151690 prefixEnd_1151690 394247023317802827518987 := by
  unfold tailWord_1151690
  simp only [CollatzResearch.WordTrace]
  refine ⟨10501396299407824459395131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28003723465087531891720349 10501396299407824459395131)
  ·
    refine ⟨15752094449111736689092697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10501396299407824459395131 15752094449111736689092697)
    ·
      refine ⟨11814070836833802516819523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15752094449111736689092697 11814070836833802516819523)
      ·
        refine ⟨17721106255250703775229285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11814070836833802516819523 17721106255250703775229285)
        ·
          refine ⟨3322707422859506957855491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17721106255250703775229285 3322707422859506957855491)
          ·
            refine ⟨4984061134289260436783237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3322707422859506957855491 4984061134289260436783237)
            ·
              refine ⟨934511462679236331896857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4984061134289260436783237 934511462679236331896857)
              ·
                refine ⟨700883597009427248922643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 934511462679236331896857 700883597009427248922643)
                ·
                  refine ⟨1051325395514140873383965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700883597009427248922643 1051325395514140873383965)
                  ·
                    refine ⟨394247023317802827518987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1051325395514140873383965 394247023317802827518987)
                    ·
                      rfl

theorem cell22_1151690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_1151690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151690 prefixEnd_1151690 := by exact prefixLift 1151690
  have htrace : WordTrace (prefixWord ++ tailWord_1151690) baseStart_1151690 baseEnd_1151690 := by
    simpa [prefixWord, tailWord_1151690, baseEnd_1151690] using wordTrace_append hprefix tailTrace_1151690
  have hstable : (prefixWord ++ tailWord_1151690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151690).length < 2 ^ (prefixWord ++ tailWord_1151690).sum := by decide
  have hdescent : baseEnd_1151690 < baseStart_1151690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151729 : List Nat := [1, 2, 2, 2, 2, 2, 1, 4, 1, 5]
def baseStart_1151729 : Nat := 118140960795 + 1151729 * 2 ^ 59
def prefixEnd_1151729 : Nat := 4983230072969 + 3 ^ 40 * 1151729 * 2
def baseEnd_1151729 : Nat := 394260373814819725793867

theorem tailTrace_1151729 : CollatzResearch.WordTrace tailWord_1151729 prefixEnd_1151729 394260373814819725793867 := by
  unfold tailWord_1151729
  simp only [CollatzResearch.WordTrace]
  refine ⟨42007007644490007498250241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28004671762993338332166827 42007007644490007498250241)
  ·
    refine ⟨31505255733367505623687681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42007007644490007498250241 31505255733367505623687681)
    ·
      refine ⟨23628941800025629217765761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31505255733367505623687681 23628941800025629217765761)
      ·
        refine ⟨17721706350019221913324321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23628941800025629217765761 17721706350019221913324321)
        ·
          refine ⟨13291279762514416434993241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17721706350019221913324321 13291279762514416434993241)
          ·
            refine ⟨9968459821885812326244931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13291279762514416434993241 9968459821885812326244931)
            ·
              refine ⟨14952689732828718489367397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9968459821885812326244931 14952689732828718489367397)
              ·
                refine ⟨2803629324905384716756387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14952689732828718489367397 2803629324905384716756387)
                ·
                  refine ⟨4205443987358077075134581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2803629324905384716756387 4205443987358077075134581)
                  ·
                    refine ⟨394260373814819725793867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4205443987358077075134581 394260373814819725793867)
                    ·
                      rfl

theorem cell22_1151729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_1151729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151729 prefixEnd_1151729 := by exact prefixLift 1151729
  have htrace : WordTrace (prefixWord ++ tailWord_1151729) baseStart_1151729 baseEnd_1151729 := by
    simpa [prefixWord, tailWord_1151729, baseEnd_1151729] using wordTrace_append hprefix tailTrace_1151729
  have hstable : (prefixWord ++ tailWord_1151729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151729).length < 2 ^ (prefixWord ++ tailWord_1151729).sum := by decide
  have hdescent : baseEnd_1151729 < baseStart_1151729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151763 : List Nat := [1, 1, 1, 2, 1, 3, 7, 1, 2, 3]
def baseStart_1151763 : Nat := 118140960795 + 1151763 * 2 ^ 59
def prefixEnd_1151763 : Nat := 4983230072969 + 3 ^ 40 * 1151763 * 2
def baseEnd_1151763 : Nat := 394272012709654970443763

theorem tailTrace_1151763 : CollatzResearch.WordTrace tailWord_1151763 prefixEnd_1151763 394272012709654970443763 := by
  unfold tailWord_1151763
  simp only [CollatzResearch.WordTrace]
  refine ⟨42008247726366831304987943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28005498484244554203325295 42008247726366831304987943)
  ·
    refine ⟨63012371589550246957481915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42008247726366831304987943 63012371589550246957481915)
    ·
      refine ⟨94518557384325370436222873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63012371589550246957481915 94518557384325370436222873)
      ·
        refine ⟨70888918038244027827167155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94518557384325370436222873 70888918038244027827167155)
        ·
          refine ⟨106333377057366041740750733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70888918038244027827167155 106333377057366041740750733)
          ·
            refine ⟨39875016396512265652781525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106333377057366041740750733 39875016396512265652781525)
            ·
              refine ⟨934570696793256226237067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 39875016396512265652781525 934570696793256226237067)
              ·
                refine ⟨1401856045189884339355601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 934570696793256226237067 1401856045189884339355601)
                ·
                  refine ⟨1051392033892413254516701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1401856045189884339355601 1051392033892413254516701)
                  ·
                    refine ⟨394272012709654970443763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1051392033892413254516701 394272012709654970443763)
                    ·
                      rfl

theorem cell22_1151763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 2, 3].length) (baseStart_1151763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151763 prefixEnd_1151763 := by exact prefixLift 1151763
  have htrace : WordTrace (prefixWord ++ tailWord_1151763) baseStart_1151763 baseEnd_1151763 := by
    simpa [prefixWord, tailWord_1151763, baseEnd_1151763] using wordTrace_append hprefix tailTrace_1151763
  have hstable : (prefixWord ++ tailWord_1151763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151763).length < 2 ^ (prefixWord ++ tailWord_1151763).sum := by decide
  have hdescent : baseEnd_1151763 < baseStart_1151763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151776 : List Nat := [2, 1, 1, 5, 1, 2, 4, 6]
def baseStart_1151776 : Nat := 118140960795 + 1151776 * 2 ^ 59
def prefixEnd_1151776 : Nat := 4983230072969 + 3 ^ 40 * 1151776 * 2
def baseEnd_1151776 : Nat := 43808495875036363318747

theorem tailTrace_1151776 : CollatzResearch.WordTrace tailWord_1151776 prefixEnd_1151776 43808495875036363318747 := by
  unfold tailWord_1151776
  simp only [CollatzResearch.WordTrace]
  refine ⟨21004360937659867262605591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28005814583546489683474121 21004360937659867262605591)
  ·
    refine ⟨31506541406489800893908387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21004360937659867262605591 31506541406489800893908387)
    ·
      refine ⟨47259812109734701340862581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31506541406489800893908387 47259812109734701340862581)
      ·
        refine ⟨4430607385287628250705867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47259812109734701340862581 4430607385287628250705867)
        ·
          refine ⟨6645911077931442376058801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4430607385287628250705867 6645911077931442376058801)
          ·
            refine ⟨4984433308448581782044101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6645911077931442376058801 4984433308448581782044101)
            ·
              refine ⟨934581245334109084133269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4984433308448581782044101 934581245334109084133269)
              ·
                refine ⟨43808495875036363318747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 934581245334109084133269 43808495875036363318747)
                ·
                  rfl

theorem cell22_1151776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 6].length) (baseStart_1151776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151776 prefixEnd_1151776 := by exact prefixLift 1151776
  have htrace : WordTrace (prefixWord ++ tailWord_1151776) baseStart_1151776 baseEnd_1151776 := by
    simpa [prefixWord, tailWord_1151776, baseEnd_1151776] using wordTrace_append hprefix tailTrace_1151776
  have hstable : (prefixWord ++ tailWord_1151776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151776).length < 2 ^ (prefixWord ++ tailWord_1151776).sum := by decide
  have hdescent : baseEnd_1151776 < baseStart_1151776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151808 : List Nat := [2, 1, 1, 2, 2, 1, 1, 8, 1, 3]
def baseStart_1151808 : Nat := 118140960795 + 1151808 * 2 ^ 59
def prefixEnd_1151808 : Nat := 4983230072969 + 3 ^ 40 * 1151808 * 2
def baseEnd_1151808 : Nat := 394287417129289853068625

theorem tailTrace_1151808 : CollatzResearch.WordTrace tailWord_1151808 prefixEnd_1151808 394287417129289853068625 := by
  unfold tailWord_1151808
  simp only [CollatzResearch.WordTrace]
  refine ⟨21004944505601901995188039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28006592674135869326917385 21004944505601901995188039)
  ·
    refine ⟨31507416758402852992782059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21004944505601901995188039 31507416758402852992782059)
    ·
      refine ⟨47261125137604279489173089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31507416758402852992782059 47261125137604279489173089)
      ·
        refine ⟨35445843853203209616879817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47261125137604279489173089 35445843853203209616879817)
        ·
          refine ⟨26584382889902407212659863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35445843853203209616879817 26584382889902407212659863)
          ·
            refine ⟨39876574334853610818989795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26584382889902407212659863 39876574334853610818989795)
            ·
              refine ⟨59814861502280416228484693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39876574334853610818989795 59814861502280416228484693)
              ·
                refine ⟨700955408229848627677555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 59814861502280416228484693 700955408229848627677555)
                ·
                  refine ⟨1051433112344772941516333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700955408229848627677555 1051433112344772941516333)
                  ·
                    refine ⟨394287417129289853068625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1051433112344772941516333 394287417129289853068625)
                    ·
                      rfl

theorem cell22_1151808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 1, 3].length) (baseStart_1151808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151808 prefixEnd_1151808 := by exact prefixLift 1151808
  have htrace : WordTrace (prefixWord ++ tailWord_1151808) baseStart_1151808 baseEnd_1151808 := by
    simpa [prefixWord, tailWord_1151808, baseEnd_1151808] using wordTrace_append hprefix tailTrace_1151808
  have hstable : (prefixWord ++ tailWord_1151808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151808).length < 2 ^ (prefixWord ++ tailWord_1151808).sum := by decide
  have hdescent : baseEnd_1151808 < baseStart_1151808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151851 : List Nat := [1, 1, 1, 1, 2, 2, 4, 5, 1, 4]
def baseStart_1151851 : Nat := 118140960795 + 1151851 * 2 ^ 59
def prefixEnd_1151851 : Nat := 4983230072969 + 3 ^ 40 * 1151851 * 2
def baseEnd_1151851 : Nat := 394302136908052074243493

theorem tailTrace_1151851 : CollatzResearch.WordTrace tailWord_1151851 prefixEnd_1151851 394302136908052074243493 := by
  unfold tailWord_1151851
  simp only [CollatzResearch.WordTrace]
  refine ⟨42011457350048022334191407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28007638233365348222794271 42011457350048022334191407)
  ·
    refine ⟨63017186025072033501287111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42011457350048022334191407 63017186025072033501287111)
    ·
      refine ⟨94525779037608050251930667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63017186025072033501287111 94525779037608050251930667)
      ·
        refine ⟨141788668556412075377896001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94525779037608050251930667 141788668556412075377896001)
        ·
          refine ⟨106341501417309056533422001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141788668556412075377896001 106341501417309056533422001)
          ·
            refine ⟨79756126062981792400066501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106341501417309056533422001 79756126062981792400066501)
            ·
              refine ⟨14954273636809086075012469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79756126062981792400066501 14954273636809086075012469)
              ·
                refine ⟨1401963153450851819532419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14954273636809086075012469 1401963153450851819532419)
                ·
                  refine ⟨2102944730176277729298629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1401963153450851819532419 2102944730176277729298629)
                  ·
                    refine ⟨394302136908052074243493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2102944730176277729298629 394302136908052074243493)
                    ·
                      rfl

theorem cell22_1151851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 4].length) (baseStart_1151851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151851 prefixEnd_1151851 := by exact prefixLift 1151851
  have htrace : WordTrace (prefixWord ++ tailWord_1151851) baseStart_1151851 baseEnd_1151851 := by
    simpa [prefixWord, tailWord_1151851, baseEnd_1151851] using wordTrace_append hprefix tailTrace_1151851
  have hstable : (prefixWord ++ tailWord_1151851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151851).length < 2 ^ (prefixWord ++ tailWord_1151851).sum := by decide
  have hdescent : baseEnd_1151851 < baseStart_1151851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151870 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1151870 : Nat := 118140960795 + 1151870 * 2 ^ 59
def prefixEnd_1151870 : Nat := 4983230072969 + 3 ^ 40 * 1151870 * 2
def baseEnd_1151870 : Nat := 394308640996342358018435

theorem tailTrace_1151870 : CollatzResearch.WordTrace tailWord_1151870 prefixEnd_1151870 394308640996342358018435 := by
  unfold tailWord_1151870
  simp only [CollatzResearch.WordTrace]
  refine ⟨5251518792122398572391633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28008100224652792386088709 5251518792122398572391633)
  ·
    refine ⟨3938639094091798929293725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5251518792122398572391633 3938639094091798929293725)
    ·
      refine ⟨1476989660284424598485147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3938639094091798929293725 1476989660284424598485147)
      ·
        refine ⟨2215484490426636897727721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1476989660284424598485147 2215484490426636897727721)
        ·
          refine ⟨1661613367819977673295791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2215484490426636897727721 1661613367819977673295791)
          ·
            refine ⟨2492420051729966509943687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1661613367819977673295791 2492420051729966509943687)
            ·
              refine ⟨3738630077594949764915531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2492420051729966509943687 3738630077594949764915531)
              ·
                refine ⟨5607945116392424647373297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3738630077594949764915531 5607945116392424647373297)
                ·
                  refine ⟨4205958837294318485529973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5607945116392424647373297 4205958837294318485529973)
                  ·
                    refine ⟨394308640996342358018435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4205958837294318485529973 394308640996342358018435)
                    ·
                      rfl

theorem cell22_1151870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1151870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151870 prefixEnd_1151870 := by exact prefixLift 1151870
  have htrace : WordTrace (prefixWord ++ tailWord_1151870) baseStart_1151870 baseEnd_1151870 := by
    simpa [prefixWord, tailWord_1151870, baseEnd_1151870] using wordTrace_append hprefix tailTrace_1151870
  have hstable : (prefixWord ++ tailWord_1151870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151870).length < 2 ^ (prefixWord ++ tailWord_1151870).sum := by decide
  have hdescent : baseEnd_1151870 < baseStart_1151870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151881 : List Nat := [1, 2, 1, 1, 5, 2, 1, 3, 1, 5]
def baseStart_1151881 : Nat := 118140960795 + 1151881 * 2 ^ 59
def prefixEnd_1151881 : Nat := 4983230072969 + 3 ^ 40 * 1151881 * 2
def baseEnd_1151881 : Nat := 394312406521141995993401

theorem tailTrace_1151881 : CollatzResearch.WordTrace tailWord_1151881 prefixEnd_1151881 394312406521141995993401 := by
  unfold tailWord_1151881
  simp only [CollatzResearch.WordTrace]
  refine ⟨42012551539939337457783497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28008367693292891638522331 42012551539939337457783497)
  ·
    refine ⟨31509413654954503093337623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42012551539939337457783497 31509413654954503093337623)
    ·
      refine ⟨47264120482431754640006435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31509413654954503093337623 47264120482431754640006435)
      ·
        refine ⟨70896180723647631960009653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47264120482431754640006435 70896180723647631960009653)
        ·
          refine ⟨6646516942841965496250905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70896180723647631960009653 6646516942841965496250905)
          ·
            refine ⟨4984887707131474122188179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6646516942841965496250905 4984887707131474122188179)
            ·
              refine ⟨7477331560697211183282269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4984887707131474122188179 7477331560697211183282269)
              ·
                refine ⟨2803999335261454193730851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7477331560697211183282269 2803999335261454193730851)
                ·
                  refine ⟨4205999002892181290596277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2803999335261454193730851 4205999002892181290596277)
                  ·
                    refine ⟨394312406521141995993401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4205999002892181290596277 394312406521141995993401)
                    ·
                      rfl

theorem cell22_1151881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 5].length) (baseStart_1151881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151881 prefixEnd_1151881 := by exact prefixLift 1151881
  have htrace : WordTrace (prefixWord ++ tailWord_1151881) baseStart_1151881 baseEnd_1151881 := by
    simpa [prefixWord, tailWord_1151881, baseEnd_1151881] using wordTrace_append hprefix tailTrace_1151881
  have hstable : (prefixWord ++ tailWord_1151881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151881).length < 2 ^ (prefixWord ++ tailWord_1151881).sum := by decide
  have hdescent : baseEnd_1151881 < baseStart_1151881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151943 : List Nat := [1, 1, 4, 1, 1, 2, 4, 2, 3, 3]
def baseStart_1151943 : Nat := 118140960795 + 1151943 * 2 ^ 59
def prefixEnd_1151943 : Nat := 4983230072969 + 3 ^ 40 * 1151943 * 2
def baseEnd_1151943 : Nat := 394333630388194500943211

theorem tailTrace_1151943 : CollatzResearch.WordTrace tailWord_1151943 prefixEnd_1151943 394333630388194500943211 := by
  unfold tailWord_1151943
  simp only [CollatzResearch.WordTrace]
  refine ⟨42014812865714722046540483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28009875243809814697693655 42014812865714722046540483)
  ·
    refine ⟨63022219298572083069810725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42014812865714722046540483 63022219298572083069810725)
    ·
      refine ⟨11816666118482265575589511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63022219298572083069810725 11816666118482265575589511)
      ·
        refine ⟨17724999177723398363384267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11816666118482265575589511 17724999177723398363384267)
        ·
          refine ⟨26587498766585097545076401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17724999177723398363384267 26587498766585097545076401)
          ·
            refine ⟨19940624074938823158807301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26587498766585097545076401 19940624074938823158807301)
            ·
              refine ⟨3738867014051029342276369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19940624074938823158807301 3738867014051029342276369)
              ·
                refine ⟨2804150260538272006707277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3738867014051029342276369 2804150260538272006707277)
                ·
                  refine ⟨1051556347701852002515229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2804150260538272006707277 1051556347701852002515229)
                  ·
                    refine ⟨394333630388194500943211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1051556347701852002515229 394333630388194500943211)
                    ·
                      rfl

theorem cell22_1151943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_1151943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151943 prefixEnd_1151943 := by exact prefixLift 1151943
  have htrace : WordTrace (prefixWord ++ tailWord_1151943) baseStart_1151943 baseEnd_1151943 := by
    simpa [prefixWord, tailWord_1151943, baseEnd_1151943] using wordTrace_append hprefix tailTrace_1151943
  have hstable : (prefixWord ++ tailWord_1151943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151943).length < 2 ^ (prefixWord ++ tailWord_1151943).sum := by decide
  have hdescent : baseEnd_1151943 < baseStart_1151943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151990 : List Nat := [5, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_1151990 : Nat := 118140960795 + 1151990 * 2 ^ 59
def prefixEnd_1151990 : Nat := 4983230072969 + 3 ^ 40 * 1151990 * 2
def baseEnd_1151990 : Nat := 131449906482900681672689

theorem tailTrace_1151990 : CollatzResearch.WordTrace tailWord_1151990 prefixEnd_1151990 131449906482900681672689 := by
  unfold tailWord_1151990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2626032943534028067093839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28011018064362966049000949 2626032943534028067093839)
  ·
    refine ⟨3939049415301042100640759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2626032943534028067093839 3939049415301042100640759)
    ·
      refine ⟨5908574122951563150961139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3939049415301042100640759 5908574122951563150961139)
      ·
        refine ⟨8862861184427344726441709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5908574122951563150961139 8862861184427344726441709)
        ·
          refine ⟨3323572944160254272415641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8862861184427344726441709 3323572944160254272415641)
          ·
            refine ⟨2492679708120190704311731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3323572944160254272415641 2492679708120190704311731)
            ·
              refine ⟨3739019562180286056467597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2492679708120190704311731 3739019562180286056467597)
              ·
                refine ⟨1402132335817607271175349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3739019562180286056467597 1402132335817607271175349)
                ·
                  refine ⟨131449906482900681672689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1402132335817607271175349 131449906482900681672689)
                  ·
                    rfl

theorem cell22_1151990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_1151990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1151990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1151990 prefixEnd_1151990 := by exact prefixLift 1151990
  have htrace : WordTrace (prefixWord ++ tailWord_1151990) baseStart_1151990 baseEnd_1151990 := by
    simpa [prefixWord, tailWord_1151990, baseEnd_1151990] using wordTrace_append hprefix tailTrace_1151990
  have hstable : (prefixWord ++ tailWord_1151990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151990).length < 2 ^ (prefixWord ++ tailWord_1151990).sum := by decide
  have hdescent : baseEnd_1151990 < baseStart_1151990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152035 : List Nat := [1, 1, 1, 4, 3, 3, 1, 4, 4]
def baseStart_1152035 : Nat := 118140960795 + 1152035 * 2 ^ 59
def prefixEnd_1152035 : Nat := 4983230072969 + 3 ^ 40 * 1152035 * 2
def baseEnd_1152035 : Nat := 131455041289445642547643

theorem tailTrace_1152035 : CollatzResearch.WordTrace tailWord_1152035 prefixEnd_1152035 131455041289445642547643 := by
  unfold tailWord_1152035
  simp only [CollatzResearch.WordTrace]
  refine ⟨42018168381381421758889559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28012112254254281172593039 42018168381381421758889559)
  ·
    refine ⟨63027252572072132638334339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42018168381381421758889559 63027252572072132638334339)
    ·
      refine ⟨94540878858108198957501509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63027252572072132638334339 94540878858108198957501509)
      ·
        refine ⟨17726414785895287304531533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94540878858108198957501509 17726414785895287304531533)
        ·
          refine ⟨6647405544710732739199325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17726414785895287304531533 6647405544710732739199325)
          ·
            refine ⟨2492777079266524777199747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6647405544710732739199325 2492777079266524777199747)
            ·
              refine ⟨3739165618899787165799621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2492777079266524777199747 3739165618899787165799621)
              ·
                refine ⟨701093553543710093587429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3739165618899787165799621 701093553543710093587429)
                ·
                  refine ⟨131455041289445642547643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 701093553543710093587429 131455041289445642547643)
                  ·
                    rfl

theorem cell22_1152035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 4].length) (baseStart_1152035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152035 prefixEnd_1152035 := by exact prefixLift 1152035
  have htrace : WordTrace (prefixWord ++ tailWord_1152035) baseStart_1152035 baseEnd_1152035 := by
    simpa [prefixWord, tailWord_1152035, baseEnd_1152035] using wordTrace_append hprefix tailTrace_1152035
  have hstable : (prefixWord ++ tailWord_1152035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152035).length < 2 ^ (prefixWord ++ tailWord_1152035).sum := by decide
  have hdescent : baseEnd_1152035 < baseStart_1152035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152050 : List Nat := [3, 2, 1, 1, 2, 2, 1, 5, 2, 3]
def baseStart_1152050 : Nat := 118140960795 + 1152050 * 2 ^ 59
def prefixEnd_1152050 : Nat := 4983230072969 + 3 ^ 40 * 1152050 * 2
def baseEnd_1152050 : Nat := 394370258674881888517883

theorem tailTrace_1152050 : CollatzResearch.WordTrace tailWord_1152050 prefixEnd_1152050 394370258674881888517883 := by
  unfold tailWord_1152050
  simp only [CollatzResearch.WordTrace]
  refine ⟨10504678869081769830171401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28012476984218052880457069 10504678869081769830171401)
  ·
    refine ⟨7878509151811327372628551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10504678869081769830171401 7878509151811327372628551)
    ·
      refine ⟨11817763727716991058942827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7878509151811327372628551 11817763727716991058942827)
      ·
        refine ⟨17726645591575486588414241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11817763727716991058942827 17726645591575486588414241)
        ·
          refine ⟨13294984193681614941310681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17726645591575486588414241 13294984193681614941310681)
          ·
            refine ⟨9971238145261211205983011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13294984193681614941310681 9971238145261211205983011)
            ·
              refine ⟨14956857217891816808974517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9971238145261211205983011 14956857217891816808974517)
              ·
                refine ⟨1402205364177357825841361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14956857217891816808974517 1402205364177357825841361)
                ·
                  refine ⟨1051654023133018369381021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1402205364177357825841361 1051654023133018369381021)
                  ·
                    refine ⟨394370258674881888517883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1051654023133018369381021 394370258674881888517883)
                    ·
                      rfl

theorem cell22_1152050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_1152050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152050 prefixEnd_1152050 := by exact prefixLift 1152050
  have htrace : WordTrace (prefixWord ++ tailWord_1152050) baseStart_1152050 baseEnd_1152050 := by
    simpa [prefixWord, tailWord_1152050, baseEnd_1152050] using wordTrace_append hprefix tailTrace_1152050
  have hstable : (prefixWord ++ tailWord_1152050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152050).length < 2 ^ (prefixWord ++ tailWord_1152050).sum := by decide
  have hdescent : baseEnd_1152050 < baseStart_1152050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152065 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 1, 6]
def baseStart_1152065 : Nat := 118140960795 + 1152065 * 2 ^ 59
def prefixEnd_1152065 : Nat := 4983230072969 + 3 ^ 40 * 1152065 * 2
def baseEnd_1152065 : Nat := 394375393481426849392837

theorem tailTrace_1152065 : CollatzResearch.WordTrace tailWord_1152065 prefixEnd_1152065 394375393481426849392837 := by
  unfold tailWord_1152065
  simp only [CollatzResearch.WordTrace]
  refine ⟨42019262571272736882481649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28012841714181824588321099 42019262571272736882481649)
  ·
    refine ⟨31514446928454552661861237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42019262571272736882481649 31514446928454552661861237)
    ·
      refine ⟨2954479399542614312049491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31514446928454552661861237 2954479399542614312049491)
      ·
        refine ⟨4431719099313921468074237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2954479399542614312049491 4431719099313921468074237)
        ·
          refine ⟨1661894662242720550527839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4431719099313921468074237 1661894662242720550527839)
          ·
            refine ⟨2492841993364080825791759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1661894662242720550527839 2492841993364080825791759)
            ·
              refine ⟨3739262990046121238687639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2492841993364080825791759 3739262990046121238687639)
              ·
                refine ⟨5608894485069181858031459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3739262990046121238687639 5608894485069181858031459)
                ·
                  refine ⟨8413341727603772787047189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5608894485069181858031459 8413341727603772787047189)
                  ·
                    refine ⟨394375393481426849392837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8413341727603772787047189 394375393481426849392837)
                    ·
                      rfl

theorem cell22_1152065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_1152065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152065 prefixEnd_1152065 := by exact prefixLift 1152065
  have htrace : WordTrace (prefixWord ++ tailWord_1152065) baseStart_1152065 baseEnd_1152065 := by
    simpa [prefixWord, tailWord_1152065, baseEnd_1152065] using wordTrace_append hprefix tailTrace_1152065
  have hstable : (prefixWord ++ tailWord_1152065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152065).length < 2 ^ (prefixWord ++ tailWord_1152065).sum := by decide
  have hdescent : baseEnd_1152065 < baseStart_1152065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152095 : List Nat := [1, 1, 2, 3, 1, 1, 6, 1, 3, 3]
def baseStart_1152095 : Nat := 118140960795 + 1152095 * 2 ^ 59
def prefixEnd_1152095 : Nat := 4983230072969 + 3 ^ 40 * 1152095 * 2
def baseEnd_1152095 : Nat := 394385663094516771142745

theorem tailTrace_1152095 : CollatzResearch.WordTrace tailWord_1152095 prefixEnd_1152095 394385663094516771142745 := by
  unfold tailWord_1152095
  simp only [CollatzResearch.WordTrace]
  refine ⟨42020356761164052006073739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28013571174109368004049159 42020356761164052006073739)
  ·
    refine ⟨63030535141746078009110609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42020356761164052006073739 63030535141746078009110609)
    ·
      refine ⟨47272901356309558506832957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63030535141746078009110609 47272901356309558506832957)
      ·
        refine ⟨17727338008616084440062359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47272901356309558506832957 17727338008616084440062359)
        ·
          refine ⟨26591007012924126660093539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17727338008616084440062359 26591007012924126660093539)
          ·
            refine ⟨39886510519386189990140309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26591007012924126660093539 39886510519386189990140309)
            ·
              refine ⟨1869680180596227655787827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39886510519386189990140309 1869680180596227655787827)
              ·
                refine ⟨2804520270894341483681741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1869680180596227655787827 2804520270894341483681741)
                ·
                  refine ⟨1051695101585378056380653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2804520270894341483681741 1051695101585378056380653)
                  ·
                    refine ⟨394385663094516771142745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1051695101585378056380653 394385663094516771142745)
                    ·
                      rfl

theorem cell22_1152095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 3].length) (baseStart_1152095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152095 prefixEnd_1152095 := by exact prefixLift 1152095
  have htrace : WordTrace (prefixWord ++ tailWord_1152095) baseStart_1152095 baseEnd_1152095 := by
    simpa [prefixWord, tailWord_1152095, baseEnd_1152095] using wordTrace_append hprefix tailTrace_1152095
  have hstable : (prefixWord ++ tailWord_1152095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152095).length < 2 ^ (prefixWord ++ tailWord_1152095).sum := by decide
  have hdescent : baseEnd_1152095 < baseStart_1152095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152129 : List Nat := [1, 2, 4, 2, 2, 1, 3, 3, 1, 3]
def baseStart_1152129 : Nat := 118140960795 + 1152129 * 2 ^ 59
def prefixEnd_1152129 : Nat := 4983230072969 + 3 ^ 40 * 1152129 * 2
def baseEnd_1152129 : Nat := 394397301989352015792641

theorem tailTrace_1152129 : CollatzResearch.WordTrace tailWord_1152129 prefixEnd_1152129 394397301989352015792641 := by
  unfold tailWord_1152129
  simp only [CollatzResearch.WordTrace]
  refine ⟨42021596843040875812811441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28014397895360583875207627 42021596843040875812811441)
  ·
    refine ⟨31516197632280656859608581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42021596843040875812811441 31516197632280656859608581)
    ·
      refine ⟨5909287056052623161176609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31516197632280656859608581 5909287056052623161176609)
      ·
        refine ⟨4431965292039467370882457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5909287056052623161176609 4431965292039467370882457)
        ·
          refine ⟨3323973969029600528161843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4431965292039467370882457 3323973969029600528161843)
          ·
            refine ⟨4985960953544400792242765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3323973969029600528161843 4985960953544400792242765)
            ·
              refine ⟨1869735357579150297091037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4985960953544400792242765 1869735357579150297091037)
              ·
                refine ⟨701150759092181361409139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1869735357579150297091037 701150759092181361409139)
                ·
                  refine ⟨1051726138638272042113709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 701150759092181361409139 1051726138638272042113709)
                  ·
                    refine ⟨394397301989352015792641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1051726138638272042113709 394397301989352015792641)
                    ·
                      rfl

theorem cell22_1152129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_1152129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152129 prefixEnd_1152129 := by exact prefixLift 1152129
  have htrace : WordTrace (prefixWord ++ tailWord_1152129) baseStart_1152129 baseEnd_1152129 := by
    simpa [prefixWord, tailWord_1152129, baseEnd_1152129] using wordTrace_append hprefix tailTrace_1152129
  have hstable : (prefixWord ++ tailWord_1152129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152129).length < 2 ^ (prefixWord ++ tailWord_1152129).sum := by decide
  have hdescent : baseEnd_1152129 < baseStart_1152129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152146 : List Nat := [3, 2, 3, 1, 1, 3, 3, 2, 1, 3]
def baseStart_1152146 : Nat := 118140960795 + 1152146 * 2 ^ 59
def prefixEnd_1152146 : Nat := 4983230072969 + 3 ^ 40 * 1152146 * 2
def baseEnd_1152146 : Nat := 394403121436769638117589

theorem tailTrace_1152146 : CollatzResearch.WordTrace tailWord_1152146 prefixEnd_1152146 394403121436769638117589 := by
  unfold tailWord_1152146
  simp only [CollatzResearch.WordTrace]
  refine ⟨10505554220994821929045073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28014811255986191810786861 10505554220994821929045073)
  ·
    refine ⟨7879165665746116446783805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10505554220994821929045073 7879165665746116446783805)
    ·
      refine ⟨2954687124654793667543927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7879165665746116446783805 2954687124654793667543927)
      ·
        refine ⟨4432030686982190501315891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2954687124654793667543927 4432030686982190501315891)
        ·
          refine ⟨6648046030473285751973837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4432030686982190501315891 6648046030473285751973837)
          ·
            refine ⟨2493017261427482156990189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6648046030473285751973837 2493017261427482156990189)
            ·
              refine ⟨934881473035305808871321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2493017261427482156990189 934881473035305808871321)
              ·
                refine ⟨701161104776479356653491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 934881473035305808871321 701161104776479356653491)
                ·
                  refine ⟨1051741657164719034980237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 701161104776479356653491 1051741657164719034980237)
                  ·
                    refine ⟨394403121436769638117589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1051741657164719034980237 394403121436769638117589)
                    ·
                      rfl

theorem cell22_1152146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_1152146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152146 prefixEnd_1152146 := by exact prefixLift 1152146
  have htrace : WordTrace (prefixWord ++ tailWord_1152146) baseStart_1152146 baseEnd_1152146 := by
    simpa [prefixWord, tailWord_1152146, baseEnd_1152146] using wordTrace_append hprefix tailTrace_1152146
  have hstable : (prefixWord ++ tailWord_1152146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152146).length < 2 ^ (prefixWord ++ tailWord_1152146).sum := by decide
  have hdescent : baseEnd_1152146 < baseStart_1152146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152159 : List Nat := [1, 1, 2, 6, 2, 2, 2, 1, 5]
def baseStart_1152159 : Nat := 118140960795 + 1152159 * 2 ^ 59
def prefixEnd_1152159 : Nat := 4983230072969 + 3 ^ 40 * 1152159 * 2
def baseEnd_1152159 : Nat := 131469190534147312514183

theorem tailTrace_1152159 : CollatzResearch.WordTrace tailWord_1152159 prefixEnd_1152159 131469190534147312514183 := by
  unfold tailWord_1152159
  simp only [CollatzResearch.WordTrace]
  refine ⟨42022691032932190936403531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28015127355288127290935687 42022691032932190936403531)
  ·
    refine ⟨63034036549398286404605297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42022691032932190936403531 63034036549398286404605297)
    ·
      refine ⟨47275527412048714803453973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63034036549398286404605297 47275527412048714803453973)
      ·
        refine ⟨2216040347439783506411905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47275527412048714803453973 2216040347439783506411905)
        ·
          refine ⟨1662030260579837629808929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2216040347439783506411905 1662030260579837629808929)
          ·
            refine ⟨1246522695434878222356697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1662030260579837629808929 1246522695434878222356697)
            ·
              refine ⟨934892021576158666767523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1246522695434878222356697 934892021576158666767523)
              ·
                refine ⟨1402338032364238000151285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 934892021576158666767523 1402338032364238000151285)
                ·
                  refine ⟨131469190534147312514183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1402338032364238000151285 131469190534147312514183)
                  ·
                    rfl

theorem cell22_1152159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 5].length) (baseStart_1152159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152159 prefixEnd_1152159 := by exact prefixLift 1152159
  have htrace : WordTrace (prefixWord ++ tailWord_1152159) baseStart_1152159 baseEnd_1152159 := by
    simpa [prefixWord, tailWord_1152159, baseEnd_1152159] using wordTrace_append hprefix tailTrace_1152159
  have hstable : (prefixWord ++ tailWord_1152159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152159).length < 2 ^ (prefixWord ++ tailWord_1152159).sum := by decide
  have hdescent : baseEnd_1152159 < baseStart_1152159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152185 : List Nat := [1, 2, 1, 4, 1, 4, 1, 2, 1, 5]
def baseStart_1152185 : Nat := 118140960795 + 1152185 * 2 ^ 59
def prefixEnd_1152185 : Nat := 4983230072969 + 3 ^ 40 * 1152185 * 2
def baseEnd_1152185 : Nat := 394416471933786536392469

theorem tailTrace_1152185 : CollatzResearch.WordTrace tailWord_1152185 prefixEnd_1152185 394416471933786536392469 := by
  unfold tailWord_1152185
  simp only [CollatzResearch.WordTrace]
  refine ⟨42023639330837997376850009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28015759553891998251233339 42023639330837997376850009)
  ·
    refine ⟨31517729498128498032637507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42023639330837997376850009 31517729498128498032637507)
    ·
      refine ⟨47276594247192747048956261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31517729498128498032637507 47276594247192747048956261)
      ·
        refine ⟨8864361421348640071679299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47276594247192747048956261 8864361421348640071679299)
        ·
          refine ⟨13296542132022960107518949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8864361421348640071679299 13296542132022960107518949)
          ·
            refine ⟨2493101649754305020159803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13296542132022960107518949 2493101649754305020159803)
            ·
              refine ⟨3739652474631457530239705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2493101649754305020159803 3739652474631457530239705)
              ·
                refine ⟨2804739355973593147679779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3739652474631457530239705 2804739355973593147679779)
                ·
                  refine ⟨4207109033960389721519669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2804739355973593147679779 4207109033960389721519669)
                  ·
                    refine ⟨394416471933786536392469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4207109033960389721519669 394416471933786536392469)
                    ·
                      rfl

theorem cell22_1152185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 5].length) (baseStart_1152185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152185 prefixEnd_1152185 := by exact prefixLift 1152185
  have htrace : WordTrace (prefixWord ++ tailWord_1152185) baseStart_1152185 baseEnd_1152185 := by
    simpa [prefixWord, tailWord_1152185, baseEnd_1152185] using wordTrace_append hprefix tailTrace_1152185
  have hstable : (prefixWord ++ tailWord_1152185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152185).length < 2 ^ (prefixWord ++ tailWord_1152185).sum := by decide
  have hdescent : baseEnd_1152185 < baseStart_1152185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152200 : List Nat := [2, 1, 3, 1, 2, 1, 4, 2, 2, 4]
def baseStart_1152200 : Nat := 118140960795 + 1152200 * 2 ^ 59
def prefixEnd_1152200 : Nat := 4983230072969 + 3 ^ 40 * 1152200 * 2
def baseEnd_1152200 : Nat := 394421606740331497267423

theorem tailTrace_1152200 : CollatzResearch.WordTrace tailWord_1152200 prefixEnd_1152200 394421606740331497267423 := by
  unfold tailWord_1152200
  simp only [CollatzResearch.WordTrace]
  refine ⟨21012093212891827469323027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28016124283855769959097369 21012093212891827469323027)
  ·
    refine ⟨31518139819337741203984541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21012093212891827469323027 31518139819337741203984541)
    ·
      refine ⟨11819302432251652951494203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31518139819337741203984541 11819302432251652951494203)
      ·
        refine ⟨17728953648377479427241305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11819302432251652951494203 17728953648377479427241305)
        ·
          refine ⟨13296715236283109570430979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17728953648377479427241305 13296715236283109570430979)
          ·
            refine ⟨19945072854424664355646469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13296715236283109570430979 19945072854424664355646469)
            ·
              refine ⟨3739701160204624566683713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19945072854424664355646469 3739701160204624566683713)
              ·
                refine ⟨2804775870153468425012785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3739701160204624566683713 2804775870153468425012785)
                ·
                  refine ⟨2103581902615101318759589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2804775870153468425012785 2103581902615101318759589)
                  ·
                    refine ⟨394421606740331497267423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2103581902615101318759589 394421606740331497267423)
                    ·
                      rfl

theorem cell22_1152200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_1152200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152200 prefixEnd_1152200 := by exact prefixLift 1152200
  have htrace : WordTrace (prefixWord ++ tailWord_1152200) baseStart_1152200 baseEnd_1152200 := by
    simpa [prefixWord, tailWord_1152200, baseEnd_1152200] using wordTrace_append hprefix tailTrace_1152200
  have hstable : (prefixWord ++ tailWord_1152200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152200).length < 2 ^ (prefixWord ++ tailWord_1152200).sum := by decide
  have hdescent : baseEnd_1152200 < baseStart_1152200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152202 : List Nat := [3, 1, 2, 1, 3, 2, 1, 4, 2, 3]
def baseStart_1152202 : Nat := 118140960795 + 1152202 * 2 ^ 59
def prefixEnd_1152202 : Nat := 4983230072969 + 3 ^ 40 * 1152202 * 2
def baseEnd_1152202 : Nat := 394422291381204158717417

theorem tailTrace_1152202 : CollatzResearch.WordTrace tailWord_1152202 prefixEnd_1152202 394422291381204158717417 := by
  unfold tailWord_1152202
  simp only [CollatzResearch.WordTrace]
  refine ⟨10506064842944102320054715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28016172914517606186812573 10506064842944102320054715)
  ·
    refine ⟨15759097264416153480082073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10506064842944102320054715 15759097264416153480082073)
    ·
      refine ⟨11819322948312115110061555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15759097264416153480082073 11819322948312115110061555)
      ·
        refine ⟨17728984422468172665092333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11819322948312115110061555 17728984422468172665092333)
        ·
          refine ⟨6648369158425564749409625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17728984422468172665092333 6648369158425564749409625)
          ·
            refine ⟨4986276868819173562057219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6648369158425564749409625 4986276868819173562057219)
            ·
              refine ⟨7479415303228760343085829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4986276868819173562057219 7479415303228760343085829)
              ·
                refine ⟨1402390369355392564328593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7479415303228760343085829 1402390369355392564328593)
                ·
                  refine ⟨1051792777016544423246445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1402390369355392564328593 1051792777016544423246445)
                  ·
                    refine ⟨394422291381204158717417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1051792777016544423246445 394422291381204158717417)
                    ·
                      rfl

theorem cell22_1152202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_1152202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152202 prefixEnd_1152202 := by exact prefixLift 1152202
  have htrace : WordTrace (prefixWord ++ tailWord_1152202) baseStart_1152202 baseEnd_1152202 := by
    simpa [prefixWord, tailWord_1152202, baseEnd_1152202] using wordTrace_append hprefix tailTrace_1152202
  have hstable : (prefixWord ++ tailWord_1152202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152202).length < 2 ^ (prefixWord ++ tailWord_1152202).sum := by decide
  have hdescent : baseEnd_1152202 < baseStart_1152202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152264 : List Nat := [2, 1, 3, 2, 4, 1, 2, 1, 3, 3]
def baseStart_1152264 : Nat := 118140960795 + 1152264 * 2 ^ 59
def prefixEnd_1152264 : Nat := 4983230072969 + 3 ^ 40 * 1152264 * 2
def baseEnd_1152264 : Nat := 394443515248256663667227

theorem tailTrace_1152264 : CollatzResearch.WordTrace tailWord_1152264 prefixEnd_1152264 394443515248256663667227 := by
  unfold tailWord_1152264
  simp only [CollatzResearch.WordTrace]
  refine ⟨21013260348775896934487923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28017680465034529245983897 21013260348775896934487923)
  ·
    refine ⟨31519890523163845401731885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21013260348775896934487923 31519890523163845401731885)
    ·
      refine ⟨11819958946186442025649457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31519890523163845401731885 11819958946186442025649457)
      ·
        refine ⟨8864969209639831519237093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11819958946186442025649457 8864969209639831519237093)
        ·
          refine ⟨1662181726807468409856955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8864969209639831519237093 1662181726807468409856955)
          ·
            refine ⟨2493272590211202614785433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1662181726807468409856955 2493272590211202614785433)
            ·
              refine ⟨1869954442658401961089075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2493272590211202614785433 1869954442658401961089075)
              ·
                refine ⟨2804931663987602941633613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1869954442658401961089075 2804931663987602941633613)
                ·
                  refine ⟨1051849373995351103112605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2804931663987602941633613 1051849373995351103112605)
                  ·
                    refine ⟨394443515248256663667227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1051849373995351103112605 394443515248256663667227)
                    ·
                      rfl

theorem cell22_1152264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_1152264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152264 prefixEnd_1152264 := by exact prefixLift 1152264
  have htrace : WordTrace (prefixWord ++ tailWord_1152264) baseStart_1152264 baseEnd_1152264 := by
    simpa [prefixWord, tailWord_1152264, baseEnd_1152264] using wordTrace_append hprefix tailTrace_1152264
  have hstable : (prefixWord ++ tailWord_1152264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152264).length < 2 ^ (prefixWord ++ tailWord_1152264).sum := by decide
  have hdescent : baseEnd_1152264 < baseStart_1152264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152298 : List Nat := [3, 1, 4, 2, 1, 3, 1, 3, 1, 3]
def baseStart_1152298 : Nat := 118140960795 + 1152298 * 2 ^ 59
def prefixEnd_1152298 : Nat := 4983230072969 + 3 ^ 40 * 1152298 * 2
def baseEnd_1152298 : Nat := 394455154143091908317123

theorem tailTrace_1152298 : CollatzResearch.WordTrace tailWord_1152298 prefixEnd_1152298 394455154143091908317123 := by
  unfold tailWord_1152298
  simp only [CollatzResearch.WordTrace]
  refine ⟨10506940194857154418928387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28018507186285745117142365 10506940194857154418928387)
  ·
    refine ⟨15760410292285731628392581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10506940194857154418928387 15760410292285731628392581)
    ·
      refine ⟨2955076929803574680323609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15760410292285731628392581 2955076929803574680323609)
      ·
        refine ⟨2216307697352681010242707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2955076929803574680323609 2216307697352681010242707)
        ·
          refine ⟨3324461546029021515364061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2216307697352681010242707 3324461546029021515364061)
          ·
            refine ⟨1246673079760883068261523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3324461546029021515364061 1246673079760883068261523)
            ·
              refine ⟨1870009619641324602392285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1246673079760883068261523 1870009619641324602392285)
              ·
                refine ⟨701253607365496725897107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1870009619641324602392285 701253607365496725897107)
                ·
                  refine ⟨1051880411048245088845661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 701253607365496725897107 1051880411048245088845661)
                  ·
                    refine ⟨394455154143091908317123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1051880411048245088845661 394455154143091908317123)
                    ·
                      rfl

theorem cell22_1152298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_1152298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152298 prefixEnd_1152298 := by exact prefixLift 1152298
  have htrace : WordTrace (prefixWord ++ tailWord_1152298) baseStart_1152298 baseEnd_1152298 := by
    simpa [prefixWord, tailWord_1152298, baseEnd_1152298] using wordTrace_append hprefix tailTrace_1152298
  have hstable : (prefixWord ++ tailWord_1152298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152298).length < 2 ^ (prefixWord ++ tailWord_1152298).sum := by decide
  have hdescent : baseEnd_1152298 < baseStart_1152298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152307 : List Nat := [1, 1, 1, 2, 5, 2, 2, 3, 1, 4]
def baseStart_1152307 : Nat := 118140960795 + 1152307 * 2 ^ 59
def prefixEnd_1152307 : Nat := 4983230072969 + 3 ^ 40 * 1152307 * 2
def baseEnd_1152307 : Nat := 394458235027018884842095

theorem tailTrace_1152307 : CollatzResearch.WordTrace tailWord_1152307 prefixEnd_1152307 394458235027018884842095 := by
  unfold tailWord_1152307
  simp only [CollatzResearch.WordTrace]
  refine ⟨42028089036396012212791175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28018726024264008141860783 42028089036396012212791175)
  ·
    refine ⟨63042133554594018319186763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42028089036396012212791175 63042133554594018319186763)
    ·
      refine ⟨94563200331891027478780145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63042133554594018319186763 94563200331891027478780145)
      ·
        refine ⟨70922400248918270609085109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94563200331891027478780145 70922400248918270609085109)
        ·
          refine ⟨6648975023336087869601729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70922400248918270609085109 6648975023336087869601729)
          ·
            refine ⟨4986731267502065902201297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6648975023336087869601729 4986731267502065902201297)
            ·
              refine ⟨3740048450626549426650973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4986731267502065902201297 3740048450626549426650973)
              ·
                refine ⟨1402518168984956034994115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3740048450626549426650973 1402518168984956034994115)
                ·
                  refine ⟨2103777253477434052491173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1402518168984956034994115 2103777253477434052491173)
                  ·
                    refine ⟨394458235027018884842095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2103777253477434052491173 394458235027018884842095)
                    ·
                      rfl

theorem cell22_1152307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 4].length) (baseStart_1152307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152307 prefixEnd_1152307 := by exact prefixLift 1152307
  have htrace : WordTrace (prefixWord ++ tailWord_1152307) baseStart_1152307 baseEnd_1152307 := by
    simpa [prefixWord, tailWord_1152307, baseEnd_1152307] using wordTrace_append hprefix tailTrace_1152307
  have hstable : (prefixWord ++ tailWord_1152307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152307).length < 2 ^ (prefixWord ++ tailWord_1152307).sum := by decide
  have hdescent : baseEnd_1152307 < baseStart_1152307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152352 : List Nat := [2, 1, 1, 3, 4, 1, 1, 3, 2, 4]
def baseStart_1152352 : Nat := 118140960795 + 1152352 * 2 ^ 59
def prefixEnd_1152352 : Nat := 4983230072969 + 3 ^ 40 * 1152352 * 2
def baseEnd_1152352 : Nat := 394473639446653767466957

theorem tailTrace_1152352 : CollatzResearch.WordTrace tailWord_1152352 prefixEnd_1152352 394473639446653767466957 := by
  unfold tailWord_1152352
  simp only [CollatzResearch.WordTrace]
  refine ⟨21014865160616492449089655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28019820214155323265452873 21014865160616492449089655)
  ·
    refine ⟨31522297740924738673634483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21014865160616492449089655 31522297740924738673634483)
    ·
      refine ⟨47283446611387108010451725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31522297740924738673634483 47283446611387108010451725)
      ·
        refine ⟨17731292479270165503919397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47283446611387108010451725 17731292479270165503919397)
        ·
          refine ⟨3324617339863156031984887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17731292479270165503919397 3324617339863156031984887)
          ·
            refine ⟨4986926009794734047977331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3324617339863156031984887 4986926009794734047977331)
            ·
              refine ⟨7480389014692101071965997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4986926009794734047977331 7480389014692101071965997)
              ·
                refine ⟨2805145880509537901987249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7480389014692101071965997 2805145880509537901987249)
                ·
                  refine ⟨2103859410382153426490437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2805145880509537901987249 2103859410382153426490437)
                  ·
                    refine ⟨394473639446653767466957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2103859410382153426490437 394473639446653767466957)
                    ·
                      rfl

theorem cell22_1152352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 2, 4].length) (baseStart_1152352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152352 prefixEnd_1152352 := by exact prefixLift 1152352
  have htrace : WordTrace (prefixWord ++ tailWord_1152352) baseStart_1152352 baseEnd_1152352 := by
    simpa [prefixWord, tailWord_1152352, baseEnd_1152352] using wordTrace_append hprefix tailTrace_1152352
  have hstable : (prefixWord ++ tailWord_1152352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152352).length < 2 ^ (prefixWord ++ tailWord_1152352).sum := by decide
  have hdescent : baseEnd_1152352 < baseStart_1152352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152373 : List Nat := [1, 3, 4, 1, 3, 2, 2, 2, 4]
def baseStart_1152373 : Nat := 118140960795 + 1152373 * 2 ^ 59
def prefixEnd_1152373 : Nat := 4983230072969 + 3 ^ 40 * 1152373 * 2
def baseEnd_1152373 : Nat := 131493609391938904230631

theorem tailTrace_1152373 : CollatzResearch.WordTrace tailWord_1152373 prefixEnd_1152373 131493609391938904230631 := by
  unfold tailWord_1152373
  simp only [CollatzResearch.WordTrace]
  refine ⟨42030496254156905484693773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28020330836104603656462515 42030496254156905484693773)
  ·
    refine ⟨15761436095308839556760165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42030496254156905484693773 15761436095308839556760165)
    ·
      refine ⟨2955269267870407416892531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15761436095308839556760165 2955269267870407416892531)
      ·
        refine ⟨4432903901805611125338797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2955269267870407416892531 4432903901805611125338797)
        ·
          refine ⟨1662338963177104172002049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4432903901805611125338797 1662338963177104172002049)
          ·
            refine ⟨1246754222382828129001537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1662338963177104172002049 1246754222382828129001537)
            ·
              refine ⟨935065666787121096751153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1246754222382828129001537 935065666787121096751153)
              ·
                refine ⟨701299250090340822563365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 935065666787121096751153 701299250090340822563365)
                ·
                  refine ⟨131493609391938904230631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 701299250090340822563365 131493609391938904230631)
                  ·
                    rfl

theorem cell22_1152373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 4].length) (baseStart_1152373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152373 prefixEnd_1152373 := by exact prefixLift 1152373
  have htrace : WordTrace (prefixWord ++ tailWord_1152373) baseStart_1152373 baseEnd_1152373 := by
    simpa [prefixWord, tailWord_1152373, baseEnd_1152373] using wordTrace_append hprefix tailTrace_1152373
  have hstable : (prefixWord ++ tailWord_1152373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152373).length < 2 ^ (prefixWord ++ tailWord_1152373).sum := by decide
  have hdescent : baseEnd_1152373 < baseStart_1152373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152380 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 1, 8]
def baseStart_1152380 : Nat := 118140960795 + 1152380 * 2 ^ 59
def prefixEnd_1152380 : Nat := 4983230072969 + 3 ^ 40 * 1152380 * 2
def baseEnd_1152380 : Nat := 394483224418871027766871

theorem tailTrace_1152380 : CollatzResearch.WordTrace tailWord_1152380 prefixEnd_1152380 394483224418871027766871 := by
  unfold tailWord_1152380
  simp only [CollatzResearch.WordTrace]
  refine ⟨21015375782565772840099297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28020501043421030453465729 21015375782565772840099297)
  ·
    refine ⟨15761531836924329630074473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21015375782565772840099297 15761531836924329630074473)
    ·
      refine ⟨11821148877693247222555855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15761531836924329630074473 11821148877693247222555855)
      ·
        refine ⟨17731723316539870833833783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11821148877693247222555855 17731723316539870833833783)
        ·
          refine ⟨26597584974809806250750675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17731723316539870833833783 26597584974809806250750675)
          ·
            refine ⟨39896377462214709376126013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26597584974809806250750675 39896377462214709376126013)
            ·
              refine ⟨14961141548330516016047255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39896377462214709376126013 14961141548330516016047255)
              ·
                refine ⟨22441712322495774024070883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14961141548330516016047255 22441712322495774024070883)
                ·
                  refine ⟨33662568483743661036106325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22441712322495774024070883 33662568483743661036106325)
                  ·
                    refine ⟨394483224418871027766871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33662568483743661036106325 394483224418871027766871)
                    ·
                      rfl

theorem cell22_1152380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_1152380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152380 prefixEnd_1152380 := by exact prefixLift 1152380
  have htrace : WordTrace (prefixWord ++ tailWord_1152380) baseStart_1152380 baseEnd_1152380 := by
    simpa [prefixWord, tailWord_1152380, baseEnd_1152380] using wordTrace_append hprefix tailTrace_1152380
  have hstable : (prefixWord ++ tailWord_1152380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152380).length < 2 ^ (prefixWord ++ tailWord_1152380).sum := by decide
  have hdescent : baseEnd_1152380 < baseStart_1152380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152416 : List Nat := [2, 1, 1, 4, 1, 2, 4, 3, 1, 3]
def baseStart_1152416 : Nat := 118140960795 + 1152416 * 2 ^ 59
def prefixEnd_1152416 : Nat := 4983230072969 + 3 ^ 40 * 1152416 * 2
def baseEnd_1152416 : Nat := 394495547954578933866761

theorem tailTrace_1152416 : CollatzResearch.WordTrace tailWord_1152416 prefixEnd_1152416 394495547954578933866761 := by
  unfold tailWord_1152416
  simp only [CollatzResearch.WordTrace]
  refine ⟨21016032296500561914254551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28021376395334082552339401 21016032296500561914254551)
  ·
    refine ⟨31524048444750842871381827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21016032296500561914254551 31524048444750842871381827)
    ·
      refine ⟨47286072667126264307072741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31524048444750842871381827 47286072667126264307072741)
      ·
        refine ⟨8866138625086174557576139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47286072667126264307072741 8866138625086174557576139)
        ·
          refine ⟨13299207937629261836364209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8866138625086174557576139 13299207937629261836364209)
          ·
            refine ⟨9974405953221946377273157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13299207937629261836364209 9974405953221946377273157)
            ·
              refine ⟨1870201116229114945738717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9974405953221946377273157 1870201116229114945738717)
              ·
                refine ⟨701325418585918104652019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1870201116229114945738717 701325418585918104652019)
                ·
                  refine ⟨1051988127878877156978029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 701325418585918104652019 1051988127878877156978029)
                  ·
                    refine ⟨394495547954578933866761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1051988127878877156978029 394495547954578933866761)
                    ·
                      rfl

theorem cell22_1152416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 1, 3].length) (baseStart_1152416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152416 prefixEnd_1152416 := by exact prefixLift 1152416
  have htrace : WordTrace (prefixWord ++ tailWord_1152416) baseStart_1152416 baseEnd_1152416 := by
    simpa [prefixWord, tailWord_1152416, baseEnd_1152416] using wordTrace_append hprefix tailTrace_1152416
  have hstable : (prefixWord ++ tailWord_1152416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152416).length < 2 ^ (prefixWord ++ tailWord_1152416).sum := by decide
  have hdescent : baseEnd_1152416 < baseStart_1152416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152429 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 7]
def baseStart_1152429 : Nat := 118140960795 + 1152429 * 2 ^ 59
def prefixEnd_1152429 : Nat := 4983230072969 + 3 ^ 40 * 1152429 * 2
def baseEnd_1152429 : Nat := 131499999373417077763907

theorem tailTrace_1152429 : CollatzResearch.WordTrace tailWord_1152429 prefixEnd_1152429 131499999373417077763907 := by
  unfold tailWord_1152429
  simp only [CollatzResearch.WordTrace]
  refine ⟨42032538741954027048732341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28021692494636018032488227 42032538741954027048732341)
  ·
    refine ⟨3940550507058190035818657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42032538741954027048732341 3940550507058190035818657)
    ·
      refine ⟨2955412880293642526863993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3940550507058190035818657 2955412880293642526863993)
      ·
        refine ⟨2216559660220231895147995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2955412880293642526863993 2216559660220231895147995)
        ·
          refine ⟨3324839490330347842721993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2216559660220231895147995 3324839490330347842721993)
          ·
            refine ⟨2493629617747760882041495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3324839490330347842721993 2493629617747760882041495)
            ·
              refine ⟨3740444426621641323062243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2493629617747760882041495 3740444426621641323062243)
              ·
                refine ⟨5610666639932461984593365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3740444426621641323062243 5610666639932461984593365)
                ·
                  refine ⟨131499999373417077763907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5610666639932461984593365 131499999373417077763907)
                  ·
                    rfl

theorem cell22_1152429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_1152429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152429 prefixEnd_1152429 := by exact prefixLift 1152429
  have htrace : WordTrace (prefixWord ++ tailWord_1152429) baseStart_1152429 baseEnd_1152429 := by
    simpa [prefixWord, tailWord_1152429, baseEnd_1152429] using wordTrace_append hprefix tailTrace_1152429
  have hstable : (prefixWord ++ tailWord_1152429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152429).length < 2 ^ (prefixWord ++ tailWord_1152429).sum := by decide
  have hdescent : baseEnd_1152429 < baseStart_1152429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152472 : List Nat := [2, 1, 2, 2, 2, 1, 2, 4, 1, 5]
def baseStart_1152472 : Nat := 118140960795 + 1152472 * 2 ^ 59
def prefixEnd_1152472 : Nat := 4983230072969 + 3 ^ 40 * 1152472 * 2
def baseEnd_1152472 : Nat := 394514717899013454466589

theorem tailTrace_1152472 : CollatzResearch.WordTrace tailWord_1152472 prefixEnd_1152472 394514717899013454466589 := by
  unfold tailWord_1152472
  simp only [CollatzResearch.WordTrace]
  refine ⟨21017053540399122696273835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28022738053865496928365113 21017053540399122696273835)
  ·
    refine ⟨31525580310598684044410753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21017053540399122696273835 31525580310598684044410753)
    ·
      refine ⟨23644185232949013033308065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31525580310598684044410753 23644185232949013033308065)
      ·
        refine ⟨17733138924711759774981049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23644185232949013033308065 17733138924711759774981049)
        ·
          refine ⟨13299854193533819831235787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17733138924711759774981049 13299854193533819831235787)
          ·
            refine ⟨19949781290300729746853681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13299854193533819831235787 19949781290300729746853681)
            ·
              refine ⟨14962335967725547310140261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19949781290300729746853681 14962335967725547310140261)
              ·
                refine ⟨2805437993948540120651299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14962335967725547310140261 2805437993948540120651299)
                ·
                  refine ⟨4208156990922810180976949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2805437993948540120651299 4208156990922810180976949)
                  ·
                    refine ⟨394514717899013454466589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4208156990922810180976949 394514717899013454466589)
                    ·
                      rfl

theorem cell22_1152472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_1152472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152472 prefixEnd_1152472 := by exact prefixLift 1152472
  have htrace : WordTrace (prefixWord ++ tailWord_1152472) baseStart_1152472 baseEnd_1152472 := by
    simpa [prefixWord, tailWord_1152472, baseEnd_1152472] using wordTrace_append hprefix tailTrace_1152472
  have hstable : (prefixWord ++ tailWord_1152472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152472).length < 2 ^ (prefixWord ++ tailWord_1152472).sum := by decide
  have hdescent : baseEnd_1152472 < baseStart_1152472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152510 : List Nat := [4, 2, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_1152510 : Nat := 118140960795 + 1152510 * 2 ^ 59
def prefixEnd_1152510 : Nat := 4983230072969 + 3 ^ 40 * 1152510 * 2
def baseEnd_1152510 : Nat := 394527726075594022016473

theorem tailTrace_1152510 : CollatzResearch.WordTrace tailWord_1152510 prefixEnd_1152510 394527726075594022016473 := by
  unfold tailWord_1152510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5254436631832572235303873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28023662036440385254953989 5254436631832572235303873)
  ·
    refine ⟨3940827473874429176477905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5254436631832572235303873 3940827473874429176477905)
    ·
      refine ⟨2955620605405821882358429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3940827473874429176477905 2955620605405821882358429)
      ·
        refine ⟨1108357727027183205884411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2955620605405821882358429 1108357727027183205884411)
        ·
          refine ⟨1662536590540774808826617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1108357727027183205884411 1662536590540774808826617)
          ·
            refine ⟨1246902442905581106619963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1662536590540774808826617 1246902442905581106619963)
            ·
              refine ⟨1870353664358371659929945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1246902442905581106619963 1870353664358371659929945)
              ·
                refine ⟨1402765248268778744947459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1870353664358371659929945 1402765248268778744947459)
                ·
                  refine ⟨2104147872403168117421189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1402765248268778744947459 2104147872403168117421189)
                  ·
                    refine ⟨394527726075594022016473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2104147872403168117421189 394527726075594022016473)
                    ·
                      rfl

theorem cell22_1152510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_1152510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152510 prefixEnd_1152510 := by exact prefixLift 1152510
  have htrace : WordTrace (prefixWord ++ tailWord_1152510) baseStart_1152510 baseEnd_1152510 := by
    simpa [prefixWord, tailWord_1152510, baseEnd_1152510] using wordTrace_append hprefix tailTrace_1152510
  have hstable : (prefixWord ++ tailWord_1152510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152510).length < 2 ^ (prefixWord ++ tailWord_1152510).sum := by decide
  have hdescent : baseEnd_1152510 < baseStart_1152510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152542 : List Nat := [4, 3, 3, 1, 1, 1, 1, 4, 4]
def baseStart_1152542 : Nat := 118140960795 + 1152542 * 2 ^ 59
def prefixEnd_1152542 : Nat := 4983230072969 + 3 ^ 40 * 1152542 * 2
def baseEnd_1152542 : Nat := 131512893443185535072125

theorem tailTrace_1152542 : CollatzResearch.WordTrace tailWord_1152542 prefixEnd_1152542 131512893443185535072125 := by
  unfold tailWord_1152542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5254582523818080918449485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28024440127029764898397253 5254582523818080918449485)
  ·
    refine ⟨1970468446431780344418557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5254582523818080918449485 1970468446431780344418557)
    ·
      refine ⟨738925667411917629156959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1970468446431780344418557 738925667411917629156959)
      ·
        refine ⟨1108388501117876443735439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 738925667411917629156959 1108388501117876443735439)
        ·
          refine ⟨1662582751676814665603159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1108388501117876443735439 1662582751676814665603159)
          ·
            refine ⟨2493874127515221998404739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1662582751676814665603159 2493874127515221998404739)
            ·
              refine ⟨3740811191272832997607109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2493874127515221998404739 3740811191272832997607109)
              ·
                refine ⟨701402098363656187051333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3740811191272832997607109 701402098363656187051333)
                ·
                  refine ⟨131512893443185535072125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 701402098363656187051333 131512893443185535072125)
                  ·
                    rfl

theorem cell22_1152542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_1152542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152542 prefixEnd_1152542 := by exact prefixLift 1152542
  have htrace : WordTrace (prefixWord ++ tailWord_1152542) baseStart_1152542 baseEnd_1152542 := by
    simpa [prefixWord, tailWord_1152542, baseEnd_1152542] using wordTrace_append hprefix tailTrace_1152542
  have hstable : (prefixWord ++ tailWord_1152542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152542).length < 2 ^ (prefixWord ++ tailWord_1152542).sum := by decide
  have hdescent : baseEnd_1152542 < baseStart_1152542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152592 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 8]
def baseStart_1152592 : Nat := 118140960795 + 1152592 * 2 ^ 59
def prefixEnd_1152592 : Nat := 4983230072969 + 3 ^ 40 * 1152592 * 2
def baseEnd_1152592 : Nat := 131518598783791047155407

theorem tailTrace_1152592 : CollatzResearch.WordTrace tailWord_1152592 prefixEnd_1152592 131518598783791047155407 := by
  unfold tailWord_1152592
  simp only [CollatzResearch.WordTrace]
  refine ⟨21019241920181752943458015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28025655893575670591277353 21019241920181752943458015)
  ·
    refine ⟨31528862880272629415187023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21019241920181752943458015 31528862880272629415187023)
    ·
      refine ⟨47293294320408944122780535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31528862880272629415187023 47293294320408944122780535)
      ·
        refine ⟨70939941480613416184170803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47293294320408944122780535 70939941480613416184170803)
        ·
          refine ⟨106409912220920124276256205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70939941480613416184170803 106409912220920124276256205)
          ·
            refine ⟨39903717082845046603596077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106409912220920124276256205 39903717082845046603596077)
            ·
              refine ⟨14963893906066892476348529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39903717082845046603596077 14963893906066892476348529)
              ·
                refine ⟨11222920429550169357261397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14963893906066892476348529 11222920429550169357261397)
                ·
                  refine ⟨131518598783791047155407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11222920429550169357261397 131518598783791047155407)
                  ·
                    rfl

theorem cell22_1152592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 8].length) (baseStart_1152592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152592 prefixEnd_1152592 := by exact prefixLift 1152592
  have htrace : WordTrace (prefixWord ++ tailWord_1152592) baseStart_1152592 baseEnd_1152592 := by
    simpa [prefixWord, tailWord_1152592, baseEnd_1152592] using wordTrace_append hprefix tailTrace_1152592
  have hstable : (prefixWord ++ tailWord_1152592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152592).length < 2 ^ (prefixWord ++ tailWord_1152592).sum := by decide
  have hdescent : baseEnd_1152592 < baseStart_1152592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152607 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 2, 9]
def baseStart_1152607 : Nat := 118140960795 + 1152607 * 2 ^ 59
def prefixEnd_1152607 : Nat := 4983230072969 + 3 ^ 40 * 1152607 * 2
def baseEnd_1152607 : Nat := 394560931157918102341175

theorem tailTrace_1152607 : CollatzResearch.WordTrace tailWord_1152607 prefixEnd_1152607 394560931157918102341175 := by
  unfold tailWord_1152607
  simp only [CollatzResearch.WordTrace]
  refine ⟨42039030935309163448712075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28026020623539442299141383 42039030935309163448712075)
  ·
    refine ⟨63058546402963745173068113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42039030935309163448712075 63058546402963745173068113)
    ·
      refine ⟨47293909802222808879801085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63058546402963745173068113 47293909802222808879801085)
      ·
        refine ⟨17735216175833553329925407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47293909802222808879801085 17735216175833553329925407)
        ·
          refine ⟨26602824263750329994888111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17735216175833553329925407 26602824263750329994888111)
          ·
            refine ⟨39904236395625494992332167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26602824263750329994888111 39904236395625494992332167)
            ·
              refine ⟨59856354593438242488498251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39904236395625494992332167 59856354593438242488498251)
              ·
                refine ⟨89784531890157363732747377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59856354593438242488498251 89784531890157363732747377)
                ·
                  refine ⟨67338398917618022799560533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89784531890157363732747377 67338398917618022799560533)
                  ·
                    refine ⟨394560931157918102341175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 67338398917618022799560533 394560931157918102341175)
                    ·
                      rfl

theorem cell22_1152607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_1152607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152607 prefixEnd_1152607 := by exact prefixLift 1152607
  have htrace : WordTrace (prefixWord ++ tailWord_1152607) baseStart_1152607 baseEnd_1152607 := by
    simpa [prefixWord, tailWord_1152607, baseEnd_1152607] using wordTrace_append hprefix tailTrace_1152607
  have hstable : (prefixWord ++ tailWord_1152607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152607).length < 2 ^ (prefixWord ++ tailWord_1152607).sum := by decide
  have hdescent : baseEnd_1152607 < baseStart_1152607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152609 : List Nat := [1, 2, 3, 1, 1, 3, 4, 1, 6]
def baseStart_1152609 : Nat := 118140960795 + 1152609 * 2 ^ 59
def prefixEnd_1152609 : Nat := 4983230072969 + 3 ^ 40 * 1152609 * 2
def baseEnd_1152609 : Nat := 131520538599596921263723

theorem tailTrace_1152609 : CollatzResearch.WordTrace tailWord_1152609 prefixEnd_1152609 131520538599596921263723 := by
  unfold tailWord_1152609
  simp only [CollatzResearch.WordTrace]
  refine ⟨42039103881301917790284881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28026069254201278526856587 42039103881301917790284881)
  ·
    refine ⟨31529327910976438342713661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42039103881301917790284881 31529327910976438342713661)
    ·
      refine ⟨11823497966616164378517623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31529327910976438342713661 11823497966616164378517623)
      ·
        refine ⟨17735246949924246567776435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11823497966616164378517623 17735246949924246567776435)
        ·
          refine ⟨26602870424886369851664653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17735246949924246567776435 26602870424886369851664653)
          ·
            refine ⟨9976076409332388694374245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26602870424886369851664653 9976076409332388694374245)
            ·
              refine ⟨1870514326749822880195171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9976076409332388694374245 1870514326749822880195171)
              ·
                refine ⟨2805771490124734320292757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1870514326749822880195171 2805771490124734320292757)
                ·
                  refine ⟨131520538599596921263723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2805771490124734320292757 131520538599596921263723)
                  ·
                    rfl

theorem cell22_1152609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 6].length) (baseStart_1152609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152609 prefixEnd_1152609 := by exact prefixLift 1152609
  have htrace : WordTrace (prefixWord ++ tailWord_1152609) baseStart_1152609 baseEnd_1152609 := by
    simpa [prefixWord, tailWord_1152609, baseEnd_1152609] using wordTrace_append hprefix tailTrace_1152609
  have hstable : (prefixWord ++ tailWord_1152609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152609).length < 2 ^ (prefixWord ++ tailWord_1152609).sum := by decide
  have hdescent : baseEnd_1152609 < baseStart_1152609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152641 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 4, 3]
def baseStart_1152641 : Nat := 118140960795 + 1152641 * 2 ^ 59
def prefixEnd_1152641 : Nat := 4983230072969 + 3 ^ 40 * 1152641 * 2
def baseEnd_1152641 : Nat := 394572570052753346991071

theorem tailTrace_1152641 : CollatzResearch.WordTrace tailWord_1152641 prefixEnd_1152641 394572570052753346991071 := by
  unfold tailWord_1152641
  simp only [CollatzResearch.WordTrace]
  refine ⟨42040271017185987255449777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28026847344790658170299851 42040271017185987255449777)
  ·
    refine ⟨31530203262889490441587333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42040271017185987255449777 31530203262889490441587333)
    ·
      refine ⟨5911913111791779457797625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31530203262889490441587333 5911913111791779457797625)
      ·
        refine ⟨4433934833843834593348219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5911913111791779457797625 4433934833843834593348219)
        ·
          refine ⟨6650902250765751890022329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4433934833843834593348219 6650902250765751890022329)
          ·
            refine ⟨4988176688074313917516747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6650902250765751890022329 4988176688074313917516747)
            ·
              refine ⟨7482265032111470876275121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4988176688074313917516747 7482265032111470876275121)
              ·
                refine ⟨5611698774083603157206341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7482265032111470876275121 5611698774083603157206341)
                ·
                  refine ⟨1052193520140675591976189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5611698774083603157206341 1052193520140675591976189)
                  ·
                    refine ⟨394572570052753346991071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1052193520140675591976189 394572570052753346991071)
                    ·
                      rfl

theorem cell22_1152641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_1152641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152641 prefixEnd_1152641 := by exact prefixLift 1152641
  have htrace : WordTrace (prefixWord ++ tailWord_1152641) baseStart_1152641 baseEnd_1152641 := by
    simpa [prefixWord, tailWord_1152641, baseEnd_1152641] using wordTrace_append hprefix tailTrace_1152641
  have hstable : (prefixWord ++ tailWord_1152641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152641).length < 2 ^ (prefixWord ++ tailWord_1152641).sum := by decide
  have hdescent : baseEnd_1152641 < baseStart_1152641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152654 : List Nat := [4, 1, 1, 3, 1, 2, 10]
def baseStart_1152654 : Nat := 118140960795 + 1152654 * 2 ^ 59
def prefixEnd_1152654 : Nat := 4983230072969 + 3 ^ 40 * 1152654 * 2
def baseEnd_1152654 : Nat := 14613963711793542459853

theorem tailTrace_1152654 : CollatzResearch.WordTrace tailWord_1152654 prefixEnd_1152654 14613963711793542459853 := by
  unfold tailWord_1152654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5255093145767361309459127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28027163444092593650448677 5255093145767361309459127)
  ·
    refine ⟨7882639718651041964188691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5255093145767361309459127 7882639718651041964188691)
    ·
      refine ⟨11823959577976562946283037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7882639718651041964188691 11823959577976562946283037)
      ·
        refine ⟨4433984841741211104856139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11823959577976562946283037 4433984841741211104856139)
        ·
          refine ⟨6650977262611816657284209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4433984841741211104856139 6650977262611816657284209)
          ·
            refine ⟨4988232946958862492963157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6650977262611816657284209 4988232946958862492963157)
            ·
              refine ⟨14613963711793542459853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4988232946958862492963157 14613963711793542459853)
              ·
                rfl

theorem cell22_1152654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 10].length) (baseStart_1152654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152654 prefixEnd_1152654 := by exact prefixLift 1152654
  have htrace : WordTrace (prefixWord ++ tailWord_1152654) baseStart_1152654 baseEnd_1152654 := by
    simpa [prefixWord, tailWord_1152654, baseEnd_1152654] using wordTrace_append hprefix tailTrace_1152654
  have hstable : (prefixWord ++ tailWord_1152654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152654).length < 2 ^ (prefixWord ++ tailWord_1152654).sum := by decide
  have hdescent : baseEnd_1152654 < baseStart_1152654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152660 : List Nat := [2, 4, 2, 2, 3, 1, 1, 1, 6]
def baseStart_1152660 : Nat := 118140960795 + 1152660 * 2 ^ 59
def prefixEnd_1152660 : Nat := 4983230072969 + 3 ^ 40 * 1152660 * 2
def baseEnd_1152660 : Nat := 131526358047014543588671

theorem tailTrace_1152660 : CollatzResearch.WordTrace tailWord_1152660 prefixEnd_1152660 131526358047014543588671 := by
  unfold tailWord_1152660
  simp only [CollatzResearch.WordTrace]
  refine ⟨21020482002058576750195717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28027309336078102333594289 21020482002058576750195717)
  ·
    refine ⟨3941340375385983140661697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21020482002058576750195717 3941340375385983140661697)
    ·
      refine ⟨2956005281539487355496273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3941340375385983140661697 2956005281539487355496273)
      ·
        refine ⟨2217003961154615516622205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2956005281539487355496273 2217003961154615516622205)
        ·
          refine ⟨831376485432980818733327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2217003961154615516622205 831376485432980818733327)
          ·
            refine ⟨1247064728149471228099991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 831376485432980818733327 1247064728149471228099991)
            ·
              refine ⟨1870597092224206842149987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1247064728149471228099991 1870597092224206842149987)
              ·
                refine ⟨2805895638336310263224981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1870597092224206842149987 2805895638336310263224981)
                ·
                  refine ⟨131526358047014543588671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2805895638336310263224981 131526358047014543588671)
                  ·
                    rfl

theorem cell22_1152660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_1152660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152660 prefixEnd_1152660 := by exact prefixLift 1152660
  have htrace : WordTrace (prefixWord ++ tailWord_1152660) baseStart_1152660 baseEnd_1152660 := by
    simpa [prefixWord, tailWord_1152660, baseEnd_1152660] using wordTrace_append hprefix tailTrace_1152660
  have hstable : (prefixWord ++ tailWord_1152660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152660).length < 2 ^ (prefixWord ++ tailWord_1152660).sum := by decide
  have hdescent : baseEnd_1152660 < baseStart_1152660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152703 : List Nat := [1, 1, 2, 2, 2, 3, 2, 5, 1, 3]
def baseStart_1152703 : Nat := 118140960795 + 1152703 * 2 ^ 59
def prefixEnd_1152703 : Nat := 4983230072969 + 3 ^ 40 * 1152703 * 2
def baseEnd_1152703 : Nat := 394593793919805851940881

theorem tailTrace_1152703 : CollatzResearch.WordTrace tailWord_1152703 prefixEnd_1152703 394593793919805851940881 := by
  unfold tailWord_1152703
  simp only [CollatzResearch.WordTrace]
  refine ⟨42042532342961371844206763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28028354895307581229471175 42042532342961371844206763)
  ·
    refine ⟨63063798514442057766310145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42042532342961371844206763 63063798514442057766310145)
    ·
      refine ⟨47297848885831543324732609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63063798514442057766310145 47297848885831543324732609)
      ·
        refine ⟨35473386664373657493549457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47297848885831543324732609 35473386664373657493549457)
        ·
          refine ⟨26605039998280243120162093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35473386664373657493549457 26605039998280243120162093)
          ·
            refine ⟨9976889999355091170060785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26605039998280243120162093 9976889999355091170060785)
            ·
              refine ⟨7482667499516318377545589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9976889999355091170060785 7482667499516318377545589)
              ·
                refine ⟨701500078079654847894899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7482667499516318377545589 701500078079654847894899)
                ·
                  refine ⟨1052250117119482271842349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 701500078079654847894899 1052250117119482271842349)
                  ·
                    refine ⟨394593793919805851940881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1052250117119482271842349 394593793919805851940881)
                    ·
                      rfl

theorem cell22_1152703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 1, 3].length) (baseStart_1152703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152703 prefixEnd_1152703 := by exact prefixLift 1152703
  have htrace : WordTrace (prefixWord ++ tailWord_1152703) baseStart_1152703 baseEnd_1152703 := by
    simpa [prefixWord, tailWord_1152703, baseEnd_1152703] using wordTrace_append hprefix tailTrace_1152703
  have hstable : (prefixWord ++ tailWord_1152703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152703).length < 2 ^ (prefixWord ++ tailWord_1152703).sum := by decide
  have hdescent : baseEnd_1152703 < baseStart_1152703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152746 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 3, 4]
def baseStart_1152746 : Nat := 118140960795 + 1152746 * 2 ^ 59
def prefixEnd_1152746 : Nat := 4983230072969 + 3 ^ 40 * 1152746 * 2
def baseEnd_1152746 : Nat := 394608513698568073115749

theorem tailTrace_1152746 : CollatzResearch.WordTrace tailWord_1152746 prefixEnd_1152746 394608513698568073115749 := by
  unfold tailWord_1152746
  simp only [CollatzResearch.WordTrace]
  refine ⟨10511025170451397547005523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28029400454537060125348061 10511025170451397547005523)
  ·
    refine ⟨15766537755677096320508285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10511025170451397547005523 15766537755677096320508285)
    ·
      refine ⟨5912451658378911120190607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15766537755677096320508285 5912451658378911120190607)
      ·
        refine ⟨8868677487568366680285911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5912451658378911120190607 8868677487568366680285911)
        ·
          refine ⟨13303016231352550020428867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8868677487568366680285911 13303016231352550020428867)
          ·
            refine ⟨19954524347028825030643301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13303016231352550020428867 19954524347028825030643301)
            ·
              refine ⟨3741473315067904693245619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19954524347028825030643301 3741473315067904693245619)
              ·
                refine ⟨5612209972601857039868429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3741473315067904693245619 5612209972601857039868429)
                ·
                  refine ⟨2104578739725696389950661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5612209972601857039868429 2104578739725696389950661)
                  ·
                    refine ⟨394608513698568073115749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2104578739725696389950661 394608513698568073115749)
                    ·
                      rfl

theorem cell22_1152746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_1152746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152746 prefixEnd_1152746 := by exact prefixLift 1152746
  have htrace : WordTrace (prefixWord ++ tailWord_1152746) baseStart_1152746 baseEnd_1152746 := by
    simpa [prefixWord, tailWord_1152746, baseEnd_1152746] using wordTrace_append hprefix tailTrace_1152746
  have hstable : (prefixWord ++ tailWord_1152746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152746).length < 2 ^ (prefixWord ++ tailWord_1152746).sum := by decide
  have hdescent : baseEnd_1152746 < baseStart_1152746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152778 : List Nat := [3, 1, 2, 2, 1, 3, 2, 4, 4]
def baseStart_1152778 : Nat := 118140960795 + 1152778 * 2 ^ 59
def prefixEnd_1152778 : Nat := 4983230072969 + 3 ^ 40 * 1152778 * 2
def baseEnd_1152778 : Nat := 131539822650843552105217

theorem tailTrace_1152778 : CollatzResearch.WordTrace tailWord_1152778 prefixEnd_1152778 131539822650843552105217 := by
  unfold tailWord_1152778
  simp only [CollatzResearch.WordTrace]
  refine ⟨10511316954422414913296747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28030178545126439768791325 10511316954422414913296747)
  ·
    refine ⟨15766975431633622369945121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10511316954422414913296747 15766975431633622369945121)
    ·
      refine ⟨11825231573725216777458841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15766975431633622369945121 11825231573725216777458841)
      ·
        refine ⟨8868923680293912583094131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11825231573725216777458841 8868923680293912583094131)
        ·
          refine ⟨13303385520440868874641197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8868923680293912583094131 13303385520440868874641197)
          ·
            refine ⟨4988769570165325827990449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13303385520440868874641197 4988769570165325827990449)
            ·
              refine ⟨3741577177623994370992837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4988769570165325827990449 3741577177623994370992837)
              ·
                refine ⟨701545720804498944561157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3741577177623994370992837 701545720804498944561157)
                ·
                  refine ⟨131539822650843552105217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 701545720804498944561157 131539822650843552105217)
                  ·
                    rfl

theorem cell22_1152778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 4].length) (baseStart_1152778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152778 prefixEnd_1152778 := by exact prefixLift 1152778
  have htrace : WordTrace (prefixWord ++ tailWord_1152778) baseStart_1152778 baseEnd_1152778 := by
    simpa [prefixWord, tailWord_1152778, baseEnd_1152778] using wordTrace_append hprefix tailTrace_1152778
  have hstable : (prefixWord ++ tailWord_1152778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152778).length < 2 ^ (prefixWord ++ tailWord_1152778).sum := by decide
  have hdescent : baseEnd_1152778 < baseStart_1152778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152791 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 1, 6]
def baseStart_1152791 : Nat := 118140960795 + 1152791 * 2 ^ 59
def prefixEnd_1152791 : Nat := 4983230072969 + 3 ^ 40 * 1152791 * 2
def baseEnd_1152791 : Nat := 394623918118202955740611

theorem tailTrace_1152791 : CollatzResearch.WordTrace tailWord_1152791 prefixEnd_1152791 394623918118202955740611 := by
  unfold tailWord_1152791
  simp only [CollatzResearch.WordTrace]
  refine ⟨42045741966642562873410227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28030494644428375248940151 42045741966642562873410227)
  ·
    refine ⟨63068612949963844310115341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42045741966642562873410227 63068612949963844310115341)
    ·
      refine ⟨23650729856236441616293253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63068612949963844310115341 23650729856236441616293253)
      ·
        refine ⟨4434511848044332803054985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23650729856236441616293253 4434511848044332803054985)
        ·
          refine ⟨3325883886033249602291239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4434511848044332803054985 3325883886033249602291239)
          ·
            refine ⟨4988825829049874403436859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3325883886033249602291239 4988825829049874403436859)
            ·
              refine ⟨7483238743574811605155289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4988825829049874403436859 7483238743574811605155289)
              ·
                refine ⟨5612429057681108703866467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7483238743574811605155289 5612429057681108703866467)
                ·
                  refine ⟨8418643586521663055799701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5612429057681108703866467 8418643586521663055799701)
                  ·
                    refine ⟨394623918118202955740611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8418643586521663055799701 394623918118202955740611)
                    ·
                      rfl

theorem cell22_1152791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_1152791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152791 prefixEnd_1152791 := by exact prefixLift 1152791
  have htrace : WordTrace (prefixWord ++ tailWord_1152791) baseStart_1152791 baseEnd_1152791 := by
    simpa [prefixWord, tailWord_1152791, baseEnd_1152791] using wordTrace_append hprefix tailTrace_1152791
  have hstable : (prefixWord ++ tailWord_1152791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152791).length < 2 ^ (prefixWord ++ tailWord_1152791).sum := by decide
  have hdescent : baseEnd_1152791 < baseStart_1152791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152825 : List Nat := [1, 2, 1, 7, 1, 1, 1, 2, 2, 4]
def baseStart_1152825 : Nat := 118140960795 + 1152825 * 2 ^ 59
def prefixEnd_1152825 : Nat := 4983230072969 + 3 ^ 40 * 1152825 * 2
def baseEnd_1152825 : Nat := 394635557013038200390507

theorem tailTrace_1152825 : CollatzResearch.WordTrace tailWord_1152825 prefixEnd_1152825 394635557013038200390507 := by
  unfold tailWord_1152825
  simp only [CollatzResearch.WordTrace]
  refine ⟨42046982048519386680147929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28031321365679591120098619 42046982048519386680147929)
  ·
    refine ⟨31535236536389540010110947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42046982048519386680147929 31535236536389540010110947)
    ·
      refine ⟨47302854804584310015166421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31535236536389540010110947 47302854804584310015166421)
      ·
        refine ⟨1108660659482444765980463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 47302854804584310015166421 1108660659482444765980463)
        ·
          refine ⟨1662990989223667148970695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1108660659482444765980463 1662990989223667148970695)
          ·
            refine ⟨2494486483835500723456043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1662990989223667148970695 2494486483835500723456043)
            ·
              refine ⟨3741729725753251085184065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2494486483835500723456043 3741729725753251085184065)
              ·
                refine ⟨2806297294314938313888049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3741729725753251085184065 2806297294314938313888049)
                ·
                  refine ⟨2104722970736203735416037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2806297294314938313888049 2104722970736203735416037)
                  ·
                    refine ⟨394635557013038200390507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2104722970736203735416037 394635557013038200390507)
                    ·
                      rfl

theorem cell22_1152825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 4].length) (baseStart_1152825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152825 prefixEnd_1152825 := by exact prefixLift 1152825
  have htrace : WordTrace (prefixWord ++ tailWord_1152825) baseStart_1152825 baseEnd_1152825 := by
    simpa [prefixWord, tailWord_1152825, baseEnd_1152825] using wordTrace_append hprefix tailTrace_1152825
  have hstable : (prefixWord ++ tailWord_1152825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152825).length < 2 ^ (prefixWord ++ tailWord_1152825).sum := by decide
  have hdescent : baseEnd_1152825 < baseStart_1152825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152844 : List Nat := [2, 2, 1, 3, 5, 1, 2, 1, 2, 3]
def baseStart_1152844 : Nat := 118140960795 + 1152844 * 2 ^ 59
def prefixEnd_1152844 : Nat := 4983230072969 + 3 ^ 40 * 1152844 * 2
def baseEnd_1152844 : Nat := 394642061101328484165449

theorem tailTrace_1152844 : CollatzResearch.WordTrace tailWord_1152844 prefixEnd_1152844 394642061101328484165449 := by
  unfold tailWord_1152844
  simp only [CollatzResearch.WordTrace]
  refine ⟨21023837517725276462544793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28031783356967035283393057 21023837517725276462544793)
  ·
    refine ⟨15767878138293957346908595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21023837517725276462544793 15767878138293957346908595)
    ·
      refine ⟨23651817207440936020362893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15767878138293957346908595 23651817207440936020362893)
      ·
        refine ⟨8869431452790351007636085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23651817207440936020362893 8869431452790351007636085)
        ·
          refine ⟨831509198699095406965883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8869431452790351007636085 831509198699095406965883)
          ·
            refine ⟨1247263798048643110448825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 831509198699095406965883 1247263798048643110448825)
            ·
              refine ⟨935447848536482332836619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1247263798048643110448825 935447848536482332836619)
              ·
                refine ⟨1403171772804723499254929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 935447848536482332836619 1403171772804723499254929)
                ·
                  refine ⟨1052378829603542624441197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1403171772804723499254929 1052378829603542624441197)
                  ·
                    refine ⟨394642061101328484165449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1052378829603542624441197 394642061101328484165449)
                    ·
                      rfl

theorem cell22_1152844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 2, 3].length) (baseStart_1152844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152844 prefixEnd_1152844 := by exact prefixLift 1152844
  have htrace : WordTrace (prefixWord ++ tailWord_1152844) baseStart_1152844 baseEnd_1152844 := by
    simpa [prefixWord, tailWord_1152844, baseEnd_1152844] using wordTrace_append hprefix tailTrace_1152844
  have hstable : (prefixWord ++ tailWord_1152844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152844).length < 2 ^ (prefixWord ++ tailWord_1152844).sum := by decide
  have hdescent : baseEnd_1152844 < baseStart_1152844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152896 : List Nat := [2, 1, 1, 2, 1, 2, 4, 3, 6]
def baseStart_1152896 : Nat := 118140960795 + 1152896 * 2 ^ 59
def prefixEnd_1152896 : Nat := 4983230072969 + 3 ^ 40 * 1152896 * 2
def baseEnd_1152896 : Nat := 131553287254672560621763

theorem tailTrace_1152896 : CollatzResearch.WordTrace tailWord_1152896 prefixEnd_1152896 131553287254672560621763 := by
  unfold tailWord_1152896
  simp only [CollatzResearch.WordTrace]
  refine ⟨21024785815631082902991271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28033047754174777203988361 21024785815631082902991271)
  ·
    refine ⟨31537178723446624354486907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21024785815631082902991271 31537178723446624354486907)
    ·
      refine ⟨47305768085169936531730361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31537178723446624354486907 47305768085169936531730361)
      ·
        refine ⟨35479326063877452398797771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47305768085169936531730361 35479326063877452398797771)
        ·
          refine ⟨53218989095816178598196657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35479326063877452398797771 53218989095816178598196657)
          ·
            refine ⟨39914241821862133948647493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53218989095816178598196657 39914241821862133948647493)
            ·
              refine ⟨7483920341599150115371405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39914241821862133948647493 7483920341599150115371405)
              ·
                refine ⟨2806470128099681293264277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7483920341599150115371405 2806470128099681293264277)
                ·
                  refine ⟨131553287254672560621763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2806470128099681293264277 131553287254672560621763)
                  ·
                    rfl

theorem cell22_1152896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 6].length) (baseStart_1152896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152896 prefixEnd_1152896 := by exact prefixLift 1152896
  have htrace : WordTrace (prefixWord ++ tailWord_1152896) baseStart_1152896 baseEnd_1152896 := by
    simpa [prefixWord, tailWord_1152896, baseEnd_1152896] using wordTrace_append hprefix tailTrace_1152896
  have hstable : (prefixWord ++ tailWord_1152896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152896).length < 2 ^ (prefixWord ++ tailWord_1152896).sum := by decide
  have hdescent : baseEnd_1152896 < baseStart_1152896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152928 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 4, 3]
def baseStart_1152928 : Nat := 118140960795 + 1152928 * 2 ^ 59
def prefixEnd_1152928 : Nat := 4983230072969 + 3 ^ 40 * 1152928 * 2
def baseEnd_1152928 : Nat := 394670816017980265065191

theorem tailTrace_1152928 : CollatzResearch.WordTrace tailWord_1152928 prefixEnd_1152928 394670816017980265065191 := by
  unfold tailWord_1152928
  simp only [CollatzResearch.WordTrace]
  refine ⟨21025369383573117635573719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28033825844764156847431625 21025369383573117635573719)
  ·
    refine ⟨31538054075359676453360579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21025369383573117635573719 31538054075359676453360579)
    ·
      refine ⟨47307081113039514680040869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31538054075359676453360579 47307081113039514680040869)
      ·
        refine ⟨8870077708694909002507663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47307081113039514680040869 8870077708694909002507663)
        ·
          refine ⟨13305116563042363503761495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8870077708694909002507663 13305116563042363503761495)
          ·
            refine ⟨19957674844563545255642243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13305116563042363503761495 19957674844563545255642243)
            ·
              refine ⟨29936512266845317883463365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19957674844563545255642243 29936512266845317883463365)
              ·
                refine ⟨5613096050033497103149381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29936512266845317883463365 5613096050033497103149381)
                ·
                  refine ⟨1052455509381280706840509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5613096050033497103149381 1052455509381280706840509)
                  ·
                    refine ⟨394670816017980265065191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1052455509381280706840509 394670816017980265065191)
                    ·
                      rfl

theorem cell22_1152928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 4, 3].length) (baseStart_1152928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152928 prefixEnd_1152928 := by exact prefixLift 1152928
  have htrace : WordTrace (prefixWord ++ tailWord_1152928) baseStart_1152928 baseEnd_1152928 := by
    simpa [prefixWord, tailWord_1152928, baseEnd_1152928] using wordTrace_append hprefix tailTrace_1152928
  have hstable : (prefixWord ++ tailWord_1152928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152928).length < 2 ^ (prefixWord ++ tailWord_1152928).sum := by decide
  have hdescent : baseEnd_1152928 < baseStart_1152928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152932 : List Nat := [2, 3, 1, 2, 1, 5, 2, 1, 1, 4]
def baseStart_1152932 : Nat := 118140960795 + 1152932 * 2 ^ 59
def prefixEnd_1152932 : Nat := 4983230072969 + 3 ^ 40 * 1152932 * 2
def baseEnd_1152932 : Nat := 394672185299725587965179

theorem tailTrace_1152932 : CollatzResearch.WordTrace tailWord_1152932 prefixEnd_1152932 394672185299725587965179 := by
  unfold tailWord_1152932
  simp only [CollatzResearch.WordTrace]
  refine ⟨21025442329565871977146525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28033923106087829302862033 21025442329565871977146525)
  ·
    refine ⟨7884540873587201991429947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21025442329565871977146525 7884540873587201991429947)
    ·
      refine ⟨11826811310380802987144921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7884540873587201991429947 11826811310380802987144921)
      ·
        refine ⟨8870108482785602240358691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11826811310380802987144921 8870108482785602240358691)
        ·
          refine ⟨13305162724178403360538037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8870108482785602240358691 13305162724178403360538037)
          ·
            refine ⟨1247359005391725315050441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13305162724178403360538037 1247359005391725315050441)
            ·
              refine ⟨935519254043793986287831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1247359005391725315050441 935519254043793986287831)
              ·
                refine ⟨1403278881065690979431747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 935519254043793986287831 1403278881065690979431747)
                ·
                  refine ⟨2104918321598536469147621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1403278881065690979431747 2104918321598536469147621)
                  ·
                    refine ⟨394672185299725587965179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2104918321598536469147621 394672185299725587965179)
                    ·
                      rfl

theorem cell22_1152932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_1152932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152932 prefixEnd_1152932 := by exact prefixLift 1152932
  have htrace : WordTrace (prefixWord ++ tailWord_1152932) baseStart_1152932 baseEnd_1152932 := by
    simpa [prefixWord, tailWord_1152932, baseEnd_1152932] using wordTrace_append hprefix tailTrace_1152932
  have hstable : (prefixWord ++ tailWord_1152932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152932).length < 2 ^ (prefixWord ++ tailWord_1152932).sum := by decide
  have hdescent : baseEnd_1152932 < baseStart_1152932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152945 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 4, 3]
def baseStart_1152945 : Nat := 118140960795 + 1152945 * 2 ^ 59
def prefixEnd_1152945 : Nat := 4983230072969 + 3 ^ 40 * 1152945 * 2
def baseEnd_1152945 : Nat := 394676635465397887390139

theorem tailTrace_1152945 : CollatzResearch.WordTrace tailWord_1152945 prefixEnd_1152945 394676635465397887390139 := by
  unfold tailWord_1152945
  simp only [CollatzResearch.WordTrace]
  refine ⟨42051358808084647174516289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28034239205389764783010859 42051358808084647174516289)
  ·
    refine ⟨31538519106063485380887217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42051358808084647174516289 31538519106063485380887217)
    ·
      refine ⟨23653889329547614035665413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31538519106063485380887217 23653889329547614035665413)
      ·
        refine ⟨4435104249290177631687265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23653889329547614035665413 4435104249290177631687265)
        ·
          refine ⟨3326328186967633223765449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4435104249290177631687265 3326328186967633223765449)
          ·
            refine ⟨2494746140225724917824087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3326328186967633223765449 2494746140225724917824087)
            ·
              refine ⟨3742119210338587376736131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2494746140225724917824087 3742119210338587376736131)
              ·
                refine ⟨5613178815507881065104197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3742119210338587376736131 5613178815507881065104197)
                ·
                  refine ⟨1052471027907727699707037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5613178815507881065104197 1052471027907727699707037)
                  ·
                    refine ⟨394676635465397887390139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1052471027907727699707037 394676635465397887390139)
                    ·
                      rfl

theorem cell22_1152945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_1152945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1152945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1152945 prefixEnd_1152945 := by exact prefixLift 1152945
  have htrace : WordTrace (prefixWord ++ tailWord_1152945) baseStart_1152945 baseEnd_1152945 := by
    simpa [prefixWord, tailWord_1152945, baseEnd_1152945] using wordTrace_append hprefix tailTrace_1152945
  have hstable : (prefixWord ++ tailWord_1152945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152945).length < 2 ^ (prefixWord ++ tailWord_1152945).sum := by decide
  have hdescent : baseEnd_1152945 < baseStart_1152945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153123 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 1, 8]
def baseStart_1153123 : Nat := 118140960795 + 1153123 * 2 ^ 59
def prefixEnd_1153123 : Nat := 4983230072969 + 3 ^ 40 * 1153123 * 2
def baseEnd_1153123 : Nat := 394737568503064756439593

theorem tailTrace_1153123 : CollatzResearch.WordTrace tailWord_1153123 prefixEnd_1153123 394737568503064756439593 := by
  unfold tailWord_1153123
  simp only [CollatzResearch.WordTrace]
  refine ⟨42057851001439783574496023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28038567334293189049664015 42057851001439783574496023)
  ·
    refine ⟨63086776502159675361744035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42057851001439783574496023 63086776502159675361744035)
    ·
      refine ⟨94630164753239513042616053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63086776502159675361744035 94630164753239513042616053)
      ·
        refine ⟨8871577945616204347745255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94630164753239513042616053 8871577945616204347745255)
        ·
          refine ⟨13307366918424306521617883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8871577945616204347745255 13307366918424306521617883)
          ·
            refine ⟨19961050377636459782426825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13307366918424306521617883 19961050377636459782426825)
            ·
              refine ⟨14970787783227344836820119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19961050377636459782426825 14970787783227344836820119)
              ·
                refine ⟨22456181674841017255230179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14970787783227344836820119 22456181674841017255230179)
                ·
                  refine ⟨33684272512261525882845269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22456181674841017255230179 33684272512261525882845269)
                  ·
                    refine ⟨394737568503064756439593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33684272512261525882845269 394737568503064756439593)
                    ·
                      rfl

theorem cell22_1153123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 8].length) (baseStart_1153123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153123 prefixEnd_1153123 := by exact prefixLift 1153123
  have htrace : WordTrace (prefixWord ++ tailWord_1153123) baseStart_1153123 baseEnd_1153123 := by
    simpa [prefixWord, tailWord_1153123, baseEnd_1153123] using wordTrace_append hprefix tailTrace_1153123
  have hstable : (prefixWord ++ tailWord_1153123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153123).length < 2 ^ (prefixWord ++ tailWord_1153123).sum := by decide
  have hdescent : baseEnd_1153123 < baseStart_1153123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153159 : List Nat := [1, 1, 4, 2, 1, 1, 5, 3, 1, 3]
def baseStart_1153159 : Nat := 118140960795 + 1153159 * 2 ^ 59
def prefixEnd_1153159 : Nat := 4983230072969 + 3 ^ 40 * 1153159 * 2
def baseEnd_1153159 : Nat := 394749892038772662539483

theorem tailTrace_1153159 : CollatzResearch.WordTrace tailWord_1153159 prefixEnd_1153159 394749892038772662539483 := by
  unfold tailWord_1153159
  simp only [CollatzResearch.WordTrace]
  refine ⟨42059164029309361722806531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28039442686206241148537687 42059164029309361722806531)
  ·
    refine ⟨63088746043964042584209797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42059164029309361722806531 63088746043964042584209797)
    ·
      refine ⟨11829139883243257984539337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63088746043964042584209797 11829139883243257984539337)
      ·
        refine ⟨8871854912432443488404503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11829139883243257984539337 8871854912432443488404503)
        ·
          refine ⟨13307782368648665232606755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8871854912432443488404503 13307782368648665232606755)
          ·
            refine ⟨19961673552972997848910133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13307782368648665232606755 19961673552972997848910133)
            ·
              refine ⟨1871406895591218548335325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19961673552972997848910133 1871406895591218548335325)
              ·
                refine ⟨701777585846706955625747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1871406895591218548335325 701777585846706955625747)
                ·
                  refine ⟨1052666378770060433438621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 701777585846706955625747 1052666378770060433438621)
                  ·
                    refine ⟨394749892038772662539483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1052666378770060433438621 394749892038772662539483)
                    ·
                      rfl

theorem cell22_1153159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_1153159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153159 prefixEnd_1153159 := by exact prefixLift 1153159
  have htrace : WordTrace (prefixWord ++ tailWord_1153159) baseStart_1153159 baseEnd_1153159 := by
    simpa [prefixWord, tailWord_1153159, baseEnd_1153159] using wordTrace_append hprefix tailTrace_1153159
  have hstable : (prefixWord ++ tailWord_1153159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153159).length < 2 ^ (prefixWord ++ tailWord_1153159).sum := by decide
  have hdescent : baseEnd_1153159 < baseStart_1153159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153176 : List Nat := [2, 1, 2, 4, 4, 1, 1, 1, 3, 3]
def baseStart_1153176 : Nat := 118140960795 + 1153176 * 2 ^ 59
def prefixEnd_1153176 : Nat := 4983230072969 + 3 ^ 40 * 1153176 * 2
def baseEnd_1153176 : Nat := 394755711486190284864431

theorem tailTrace_1153176 : CollatzResearch.WordTrace tailWord_1153176 prefixEnd_1153176 394755711486190284864431 := by
  unfold tailWord_1153176
  simp only [CollatzResearch.WordTrace]
  refine ⟨21029892035123886813087691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28039856046831849084116921 21029892035123886813087691)
  ·
    refine ⟨31544838052685830219631537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21029892035123886813087691 31544838052685830219631537)
    ·
      refine ⟨23658628539514372664723653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31544838052685830219631537 23658628539514372664723653)
      ·
        refine ⟨4435992851158944874635685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23658628539514372664723653 4435992851158944874635685)
        ·
          refine ⟨831748659592302163994191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4435992851158944874635685 831748659592302163994191)
          ·
            refine ⟨1247622989388453245991287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 831748659592302163994191 1247622989388453245991287)
            ·
              refine ⟨1871434484082679868986931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1247622989388453245991287 1871434484082679868986931)
              ·
                refine ⟨2807151726124019803480397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1871434484082679868986931 2807151726124019803480397)
                ·
                  refine ⟨1052681897296507426305149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2807151726124019803480397 1052681897296507426305149)
                  ·
                    refine ⟨394755711486190284864431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1052681897296507426305149 394755711486190284864431)
                    ·
                      rfl

theorem cell22_1153176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 3, 3].length) (baseStart_1153176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153176 prefixEnd_1153176 := by exact prefixLift 1153176
  have htrace : WordTrace (prefixWord ++ tailWord_1153176) baseStart_1153176 baseEnd_1153176 := by
    simpa [prefixWord, tailWord_1153176, baseEnd_1153176] using wordTrace_append hprefix tailTrace_1153176
  have hstable : (prefixWord ++ tailWord_1153176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153176).length < 2 ^ (prefixWord ++ tailWord_1153176).sum := by decide
  have hdescent : baseEnd_1153176 < baseStart_1153176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153234 : List Nat := [3, 2, 2, 2, 1, 3, 1, 4, 4]
def baseStart_1153234 : Nat := 118140960795 + 1153234 * 2 ^ 59
def prefixEnd_1153234 : Nat := 4983230072969 + 3 ^ 40 * 1153234 * 2
def baseEnd_1153234 : Nat := 131591855357165822304751

theorem tailTrace_1153234 : CollatzResearch.WordTrace tailWord_1153234 prefixEnd_1153234 131591855357165822304751 := by
  unfold tailWord_1153234
  simp only [CollatzResearch.WordTrace]
  refine ⟨10515474876009412382946689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28041266336025099687857837 10515474876009412382946689)
  ·
    refine ⟨7886606157007059287210017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10515474876009412382946689 7886606157007059287210017)
    ·
      refine ⟨5914954617755294465407513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7886606157007059287210017 5914954617755294465407513)
      ·
        refine ⟨4436215963316470849055635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5914954617755294465407513 4436215963316470849055635)
        ·
          refine ⟨6654323944974706273583453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4436215963316470849055635 6654323944974706273583453)
          ·
            refine ⟨2495371479365514852593795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6654323944974706273583453 2495371479365514852593795)
            ·
              refine ⟨3743057219048272278890693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2495371479365514852593795 3743057219048272278890693)
              ·
                refine ⟨701823228571551052292005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3743057219048272278890693 701823228571551052292005)
                ·
                  refine ⟨131591855357165822304751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 701823228571551052292005 131591855357165822304751)
                  ·
                    rfl

theorem cell22_1153234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_1153234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153234 prefixEnd_1153234 := by exact prefixLift 1153234
  have htrace : WordTrace (prefixWord ++ tailWord_1153234) baseStart_1153234 baseEnd_1153234 := by
    simpa [prefixWord, tailWord_1153234, baseEnd_1153234] using wordTrace_append hprefix tailTrace_1153234
  have hstable : (prefixWord ++ tailWord_1153234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153234).length < 2 ^ (prefixWord ++ tailWord_1153234).sum := by decide
  have hdescent : baseEnd_1153234 < baseStart_1153234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153294 : List Nat := [4, 1, 1, 2, 1, 2, 4, 1, 3, 3]
def baseStart_1153294 : Nat := 118140960795 + 1153294 * 2 ^ 59
def prefixEnd_1153294 : Nat := 4983230072969 + 3 ^ 40 * 1153294 * 2
def baseEnd_1153294 : Nat := 394796105297677310414069

theorem tailTrace_1153294 : CollatzResearch.WordTrace tailWord_1153294 prefixEnd_1153294 394796105297677310414069 := by
  unfold tailWord_1153294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5258010985477534972371367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28042725255880186519313957 5258010985477534972371367)
  ·
    refine ⟨7887016478216302458557051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5258010985477534972371367 7887016478216302458557051)
    ·
      refine ⟨11830524717324453687835577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7887016478216302458557051 11830524717324453687835577)
      ·
        refine ⟨8872893537993340265876683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11830524717324453687835577 8872893537993340265876683)
        ·
          refine ⟨13309340306990010398815025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8872893537993340265876683 13309340306990010398815025)
          ·
            refine ⟨9982005230242507799111269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13309340306990010398815025 9982005230242507799111269)
            ·
              refine ⟨1871625980670470212333363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9982005230242507799111269 1871625980670470212333363)
              ·
                refine ⟨2807438971005705318500045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1871625980670470212333363 2807438971005705318500045)
                ·
                  refine ⟨1052789614127139494437517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2807438971005705318500045 1052789614127139494437517)
                  ·
                    refine ⟨394796105297677310414069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1052789614127139494437517 394796105297677310414069)
                    ·
                      rfl

theorem cell22_1153294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_1153294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153294 prefixEnd_1153294 := by exact prefixLift 1153294
  have htrace : WordTrace (prefixWord ++ tailWord_1153294) baseStart_1153294 baseEnd_1153294 := by
    simpa [prefixWord, tailWord_1153294, baseEnd_1153294] using wordTrace_append hprefix tailTrace_1153294
  have hstable : (prefixWord ++ tailWord_1153294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153294).length < 2 ^ (prefixWord ++ tailWord_1153294).sum := by decide
  have hdescent : baseEnd_1153294 < baseStart_1153294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153335 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 8]
def baseStart_1153335 : Nat := 118140960795 + 1153335 * 2 ^ 59
def prefixEnd_1153335 : Nat := 4983230072969 + 3 ^ 40 * 1153335 * 2
def baseEnd_1153335 : Nat := 131603380145188956712981

theorem tailTrace_1153335 : CollatzResearch.WordTrace tailWord_1153335 prefixEnd_1153335 131603380145188956712981 := by
  unfold tailWord_1153335
  simp only [CollatzResearch.WordTrace]
  refine ⟨42065583276671743781213459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28043722184447829187475639 42065583276671743781213459)
  ·
    refine ⟨63098374915007615671820189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42065583276671743781213459 63098374915007615671820189)
    ·
      refine ⟨23661890593127855876932571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63098374915007615671820189 23661890593127855876932571)
      ·
        refine ⟨35492835889691783815398857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23661890593127855876932571 35492835889691783815398857)
        ·
          refine ⟨26619626917268837861549143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35492835889691783815398857 26619626917268837861549143)
          ·
            refine ⟨39929440375903256792323715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26619626917268837861549143 39929440375903256792323715)
            ·
              refine ⟨59894160563854885188485573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39929440375903256792323715 59894160563854885188485573)
              ·
                refine ⟨11230155105722790972841045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59894160563854885188485573 11230155105722790972841045)
                ·
                  refine ⟨131603380145188956712981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11230155105722790972841045 131603380145188956712981)
                  ·
                    rfl

theorem cell22_1153335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 8].length) (baseStart_1153335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153335 prefixEnd_1153335 := by exact prefixLift 1153335
  have htrace : WordTrace (prefixWord ++ tailWord_1153335) baseStart_1153335 baseEnd_1153335 := by
    simpa [prefixWord, tailWord_1153335, baseEnd_1153335] using wordTrace_append hprefix tailTrace_1153335
  have hstable : (prefixWord ++ tailWord_1153335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153335).length < 2 ^ (prefixWord ++ tailWord_1153335).sum := by decide
  have hdescent : baseEnd_1153335 < baseStart_1153335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153345 : List Nat := [1, 2, 5, 2, 2, 1, 3, 2, 1, 3]
def baseStart_1153345 : Nat := 118140960795 + 1153345 * 2 ^ 59
def prefixEnd_1153345 : Nat := 4983230072969 + 3 ^ 40 * 1153345 * 2
def baseEnd_1153345 : Nat := 394813563639930177388913

theorem tailTrace_1153345 : CollatzResearch.WordTrace tailWord_1153345 prefixEnd_1153345 394813563639930177388913 := by
  unfold tailWord_1153345
  simp only [CollatzResearch.WordTrace]
  refine ⟨42065948006635515489077489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28043965337757010326051659 42065948006635515489077489)
  ·
    refine ⟨31549461004976636616808117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42065948006635515489077489 31549461004976636616808117)
    ·
      refine ⟨2957761969216559682825761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31549461004976636616808117 2957761969216559682825761)
      ·
        refine ⟨2218321476912419762119321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2957761969216559682825761 2218321476912419762119321)
        ·
          refine ⟨1663741107684314821589491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2218321476912419762119321 1663741107684314821589491)
          ·
            refine ⟨2495611661526472232384237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1663741107684314821589491 2495611661526472232384237)
            ·
              refine ⟨935854373072427087144089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2495611661526472232384237 935854373072427087144089)
              ·
                refine ⟨701890779804320315358067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 935854373072427087144089 701890779804320315358067)
                ·
                  refine ⟨1052836169706480473037101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 701890779804320315358067 1052836169706480473037101)
                  ·
                    refine ⟨394813563639930177388913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1052836169706480473037101 394813563639930177388913)
                    ·
                      rfl

theorem cell22_1153345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_1153345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153345 prefixEnd_1153345 := by exact prefixLift 1153345
  have htrace : WordTrace (prefixWord ++ tailWord_1153345) baseStart_1153345 baseEnd_1153345 := by
    simpa [prefixWord, tailWord_1153345, baseEnd_1153345] using wordTrace_append hprefix tailTrace_1153345
  have hstable : (prefixWord ++ tailWord_1153345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153345).length < 2 ^ (prefixWord ++ tailWord_1153345).sum := by decide
  have hdescent : baseEnd_1153345 < baseStart_1153345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153352 : List Nat := [2, 1, 3, 1, 1, 2, 5, 1, 6]
def baseStart_1153352 : Nat := 118140960795 + 1153352 * 2 ^ 59
def prefixEnd_1153352 : Nat := 4983230072969 + 3 ^ 40 * 1153352 * 2
def baseEnd_1153352 : Nat := 131605319960994830821297

theorem tailTrace_1153352 : CollatzResearch.WordTrace tailWord_1153352 prefixEnd_1153352 131605319960994830821297 := by
  unfold tailWord_1153352
  simp only [CollatzResearch.WordTrace]
  refine ⟨21033101658805077842291155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28044135545073437123054873 21033101658805077842291155)
  ·
    refine ⟨31549652488207616763436733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21033101658805077842291155 31549652488207616763436733)
    ·
      refine ⟨11831119683077856286288775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31549652488207616763436733 11831119683077856286288775)
      ·
        refine ⟨17746679524616784429433163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11831119683077856286288775 17746679524616784429433163)
        ·
          refine ⟨26620019286925176644149745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17746679524616784429433163 26620019286925176644149745)
          ·
            refine ⟨19965014465193882483112309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26620019286925176644149745 19965014465193882483112309)
            ·
              refine ⟨1871720106111926482791779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19965014465193882483112309 1871720106111926482791779)
              ·
                refine ⟨2807580159167889724187669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1871720106111926482791779 2807580159167889724187669)
                ·
                  refine ⟨131605319960994830821297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2807580159167889724187669 131605319960994830821297)
                  ·
                    rfl

theorem cell22_1153352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 6].length) (baseStart_1153352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153352 prefixEnd_1153352 := by exact prefixLift 1153352
  have htrace : WordTrace (prefixWord ++ tailWord_1153352) baseStart_1153352 baseEnd_1153352 := by
    simpa [prefixWord, tailWord_1153352, baseEnd_1153352] using wordTrace_append hprefix tailTrace_1153352
  have hstable : (prefixWord ++ tailWord_1153352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153352).length < 2 ^ (prefixWord ++ tailWord_1153352).sum := by decide
  have hdescent : baseEnd_1153352 < baseStart_1153352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153367 : List Nat := [1, 1, 3, 2, 3, 1, 2, 3, 1, 5]
def baseStart_1153367 : Nat := 118140960795 + 1153367 * 2 ^ 59
def prefixEnd_1153367 : Nat := 4983230072969 + 3 ^ 40 * 1153367 * 2
def baseEnd_1153367 : Nat := 394821094689529453338845

theorem tailTrace_1153367 : CollatzResearch.WordTrace tailWord_1153367 prefixEnd_1153367 394821094689529453338845 := by
  unfold tailWord_1153367
  simp only [CollatzResearch.WordTrace]
  refine ⟨42066750412555813246378355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28044500275037208830918903 42066750412555813246378355)
  ·
    refine ⟨63100125618833719869567533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42066750412555813246378355 63100125618833719869567533)
    ·
      refine ⟨23662547107062644951087825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63100125618833719869567533 23662547107062644951087825)
      ·
        refine ⟨17746910330296983713315869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23662547107062644951087825 17746910330296983713315869)
        ·
          refine ⟨6655091373861368892493451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17746910330296983713315869 6655091373861368892493451)
          ·
            refine ⟨9982637060792053338740177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6655091373861368892493451 9982637060792053338740177)
            ·
              refine ⟨7486977795594040004055133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9982637060792053338740177 7486977795594040004055133)
              ·
                refine ⟨2807616673347765001520675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7486977795594040004055133 2807616673347765001520675)
                ·
                  refine ⟨4211425010021647502281013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807616673347765001520675 4211425010021647502281013)
                  ·
                    refine ⟨394821094689529453338845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4211425010021647502281013 394821094689529453338845)
                    ·
                      rfl

theorem cell22_1153367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_1153367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153367 prefixEnd_1153367 := by exact prefixLift 1153367
  have htrace : WordTrace (prefixWord ++ tailWord_1153367) baseStart_1153367 baseEnd_1153367 := by
    simpa [prefixWord, tailWord_1153367, baseEnd_1153367] using wordTrace_append hprefix tailTrace_1153367
  have hstable : (prefixWord ++ tailWord_1153367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153367).length < 2 ^ (prefixWord ++ tailWord_1153367).sum := by decide
  have hdescent : baseEnd_1153367 < baseStart_1153367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153384 : List Nat := [2, 1, 4, 2, 2, 2, 1, 2, 1, 5]
def baseStart_1153384 : Nat := 118140960795 + 1153384 * 2 ^ 59
def prefixEnd_1153384 : Nat := 4983230072969 + 3 ^ 40 * 1153384 * 2
def baseEnd_1153384 : Nat := 394826914136947075663793

theorem tailTrace_1153384 : CollatzResearch.WordTrace tailWord_1153384 prefixEnd_1153384 394826914136947075663793 := by
  unfold tailWord_1153384
  simp only [CollatzResearch.WordTrace]
  refine ⟨21033685226747112574873603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28044913635662816766498137 21033685226747112574873603)
  ·
    refine ⟨31550527840120668862310405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21033685226747112574873603 31550527840120668862310405)
    ·
      refine ⟨5915723970022625411683201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31550527840120668862310405 5915723970022625411683201)
      ·
        refine ⟨4436792977516969058762401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5915723970022625411683201 4436792977516969058762401)
        ·
          refine ⟨3327594733137726794071801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4436792977516969058762401 3327594733137726794071801)
          ·
            refine ⟨2495696049853295095553851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3327594733137726794071801 2495696049853295095553851)
            ·
              refine ⟨3743544074779942643330777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2495696049853295095553851 3743544074779942643330777)
              ·
                refine ⟨2807658056084956982498083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3743544074779942643330777 2807658056084956982498083)
                ·
                  refine ⟨4211487084127435473747125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807658056084956982498083 4211487084127435473747125)
                  ·
                    refine ⟨394826914136947075663793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4211487084127435473747125 394826914136947075663793)
                    ·
                      rfl

theorem cell22_1153384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_1153384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153384 prefixEnd_1153384 := by exact prefixLift 1153384
  have htrace : WordTrace (prefixWord ++ tailWord_1153384) baseStart_1153384 baseEnd_1153384 := by
    simpa [prefixWord, tailWord_1153384, baseEnd_1153384] using wordTrace_append hprefix tailTrace_1153384
  have hstable : (prefixWord ++ tailWord_1153384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153384).length < 2 ^ (prefixWord ++ tailWord_1153384).sum := by decide
  have hdescent : baseEnd_1153384 < baseStart_1153384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153397 : List Nat := [1, 3, 4, 1, 2, 11]
def baseStart_1153397 : Nat := 118140960795 + 1153397 * 2 ^ 59
def prefixEnd_1153397 : Nat := 4983230072969 + 3 ^ 40 * 1153397 * 2
def baseEnd_1153397 : Nat := 4874461287686658951713

theorem tailTrace_1153397 : CollatzResearch.WordTrace tailWord_1153397 prefixEnd_1153397 4874461287686658951713 := by
  unfold tailWord_1153397
  simp only [CollatzResearch.WordTrace]
  refine ⟨42067844602447128369970445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28045229734964752246646963 42067844602447128369970445)
  ·
    refine ⟨15775441725917673138738917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42067844602447128369970445 15775441725917673138738917)
    ·
      refine ⟨2957895323609563713513547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15775441725917673138738917 2957895323609563713513547)
      ·
        refine ⟨4436842985414345570270321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2957895323609563713513547 4436842985414345570270321)
        ·
          refine ⟨3327632239060759177702741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4436842985414345570270321 3327632239060759177702741)
          ·
            refine ⟨4874461287686658951713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3327632239060759177702741 4874461287686658951713)
            ·
              rfl

theorem cell22_1153397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 11].length) (baseStart_1153397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153397 prefixEnd_1153397 := by exact prefixLift 1153397
  have htrace : WordTrace (prefixWord ++ tailWord_1153397) baseStart_1153397 baseEnd_1153397 := by
    simpa [prefixWord, tailWord_1153397, baseEnd_1153397] using wordTrace_append hprefix tailTrace_1153397
  have hstable : (prefixWord ++ tailWord_1153397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153397).length < 2 ^ (prefixWord ++ tailWord_1153397).sum := by decide
  have hdescent : baseEnd_1153397 < baseStart_1153397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153566 : List Nat := [4, 3, 3, 12]
def baseStart_1153566 : Nat := 118140960795 + 1153566 * 2 ^ 59
def prefixEnd_1153566 : Nat := 4983230072969 + 3 ^ 40 * 1153566 * 2
def baseEnd_1153566 : Nat := 541686167978544948715

theorem tailTrace_1153566 : CollatzResearch.WordTrace tailWord_1153566 prefixEnd_1153566 541686167978544948715 := by
  unfold tailWord_1153566
  simp only [CollatzResearch.WordTrace]
  refine ⟨5259251067354358779109069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28049339025889913488581701 5259251067354358779109069)
  ·
    refine ⟨1972219150257884542165901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5259251067354358779109069 1972219150257884542165901)
    ·
      refine ⟨739582181346706703312213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1972219150257884542165901 739582181346706703312213)
      ·
        refine ⟨541686167978544948715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 739582181346706703312213 541686167978544948715)
        ·
          rfl

theorem cell22_1153566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 12].length) (baseStart_1153566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153566 prefixEnd_1153566 := by exact prefixLift 1153566
  have htrace : WordTrace (prefixWord ++ tailWord_1153566) baseStart_1153566 baseEnd_1153566 := by
    simpa [prefixWord, tailWord_1153566, baseEnd_1153566] using wordTrace_append hprefix tailTrace_1153566
  have hstable : (prefixWord ++ tailWord_1153566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153566).length < 2 ^ (prefixWord ++ tailWord_1153566).sum := by decide
  have hdescent : baseEnd_1153566 < baseStart_1153566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153572 : List Nat := [2, 3, 1, 5, 1, 2, 2, 2, 4]
def baseStart_1153572 : Nat := 118140960795 + 1153572 * 2 ^ 59
def prefixEnd_1153572 : Nat := 4983230072969 + 3 ^ 40 * 1153572 * 2
def baseEnd_1153572 : Nat := 131630423459659083987739

theorem tailTrace_1153572 : CollatzResearch.WordTrace tailWord_1153572 prefixEnd_1153572 131630423459659083987739 := by
  unfold tailWord_1153572
  simp only [CollatzResearch.WordTrace]
  refine ⟨21037113688406566628795485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28049484917875422171727313 21037113688406566628795485)
  ·
    refine ⟨7888917633152462485798307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21037113688406566628795485 7888917633152462485798307)
    ·
      refine ⟨11833376449728693728697461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7888917633152462485798307 11833376449728693728697461)
      ·
        refine ⟨1109379042162065037065387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11833376449728693728697461 1109379042162065037065387)
        ·
          refine ⟨1664068563243097555598081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109379042162065037065387 1664068563243097555598081)
          ·
            refine ⟨1248051422432323166698561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1664068563243097555598081 1248051422432323166698561)
            ·
              refine ⟨936038566824242375023921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1248051422432323166698561 936038566824242375023921)
              ·
                refine ⟨702028925118181781267941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 936038566824242375023921 702028925118181781267941)
                ·
                  refine ⟨131630423459659083987739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 702028925118181781267941 131630423459659083987739)
                  ·
                    rfl

theorem cell22_1153572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_1153572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153572 prefixEnd_1153572 := by exact prefixLift 1153572
  have htrace : WordTrace (prefixWord ++ tailWord_1153572) baseStart_1153572 baseEnd_1153572 := by
    simpa [prefixWord, tailWord_1153572, baseEnd_1153572] using wordTrace_append hprefix tailTrace_1153572
  have hstable : (prefixWord ++ tailWord_1153572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153572).length < 2 ^ (prefixWord ++ tailWord_1153572).sum := by decide
  have hdescent : baseEnd_1153572 < baseStart_1153572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153671 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 6, 3]
def baseStart_1153671 : Nat := 118140960795 + 1153671 * 2 ^ 59
def prefixEnd_1153671 : Nat := 4983230072969 + 3 ^ 40 * 1153671 * 2
def baseEnd_1153671 : Nat := 394925160102173993737913

theorem tailTrace_1153671 : CollatzResearch.WordTrace tailWord_1153671 prefixEnd_1153671 394925160102173993737913 := by
  unfold tailWord_1153671
  simp only [CollatzResearch.WordTrace]
  refine ⟨42077838203454473165444867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28051892135636315443629911 42077838203454473165444867)
  ·
    refine ⟨63116757305181709748167301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42077838203454473165444867 63116757305181709748167301)
    ·
      refine ⟨11834391994721570577781369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63116757305181709748167301 11834391994721570577781369)
      ·
        refine ⟨8875793996041177933336027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11834391994721570577781369 8875793996041177933336027)
        ·
          refine ⟨13313690994061766900004041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8875793996041177933336027 13313690994061766900004041)
          ·
            refine ⟨9985268245546325175003031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13313690994061766900004041 9985268245546325175003031)
            ·
              refine ⟨14977902368319487762504547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9985268245546325175003031 14977902368319487762504547)
              ·
                refine ⟨22466853552479231643756821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14977902368319487762504547 22466853552479231643756821)
                ·
                  refine ⟨1053133760272463983301101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22466853552479231643756821 1053133760272463983301101)
                  ·
                    refine ⟨394925160102173993737913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1053133760272463983301101 394925160102173993737913)
                    ·
                      rfl

theorem cell22_1153671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_1153671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153671 prefixEnd_1153671 := by exact prefixLift 1153671
  have htrace : WordTrace (prefixWord ++ tailWord_1153671) baseStart_1153671 baseEnd_1153671 := by
    simpa [prefixWord, tailWord_1153671, baseEnd_1153671] using wordTrace_append hprefix tailTrace_1153671
  have hstable : (prefixWord ++ tailWord_1153671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153671).length < 2 ^ (prefixWord ++ tailWord_1153671).sum := by decide
  have hdescent : baseEnd_1153671 < baseStart_1153671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153688 : List Nat := [2, 1, 2, 4, 1, 1, 2, 4, 2, 3]
def baseStart_1153688 : Nat := 118140960795 + 1153688 * 2 ^ 59
def prefixEnd_1153688 : Nat := 4983230072969 + 3 ^ 40 * 1153688 * 2
def baseEnd_1153688 : Nat := 394930979549591616062861

theorem tailTrace_1153688 : CollatzResearch.WordTrace tailWord_1153688 prefixEnd_1153688 394930979549591616062861 := by
  unfold tailWord_1153688
  simp only [CollatzResearch.WordTrace]
  refine ⟨21039229122196442534406859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28052305496261923379209145 21039229122196442534406859)
  ·
    refine ⟨31558843683294663801610289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21039229122196442534406859 31558843683294663801610289)
    ·
      refine ⟨23669132762470997851207717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31558843683294663801610289 23669132762470997851207717)
      ·
        refine ⟨4437962392963312097101447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23669132762470997851207717 4437962392963312097101447)
        ·
          refine ⟨6656943589444968145652171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4437962392963312097101447 6656943589444968145652171)
          ·
            refine ⟨9985415384167452218478257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6656943589444968145652171 9985415384167452218478257)
            ·
              refine ⟨7489061538125589163858693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9985415384167452218478257 7489061538125589163858693)
              ·
                refine ⟨1404199038398547968223505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7489061538125589163858693 1404199038398547968223505)
                ·
                  refine ⟨1053149278798910976167629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1404199038398547968223505 1053149278798910976167629)
                  ·
                    refine ⟨394930979549591616062861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1053149278798910976167629 394930979549591616062861)
                    ·
                      rfl

theorem cell22_1153688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_1153688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153688 prefixEnd_1153688 := by exact prefixLift 1153688
  have htrace : WordTrace (prefixWord ++ tailWord_1153688) baseStart_1153688 baseEnd_1153688 := by
    simpa [prefixWord, tailWord_1153688, baseEnd_1153688] using wordTrace_append hprefix tailTrace_1153688
  have hstable : (prefixWord ++ tailWord_1153688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153688).length < 2 ^ (prefixWord ++ tailWord_1153688).sum := by decide
  have hdescent : baseEnd_1153688 < baseStart_1153688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153690 : List Nat := [3, 1, 1, 6, 1, 2, 1, 1, 6]
def baseStart_1153690 : Nat := 118140960795 + 1153690 * 2 ^ 59
def prefixEnd_1153690 : Nat := 4983230072969 + 3 ^ 40 * 1153690 * 2
def baseEnd_1153690 : Nat := 131643888063488092504285

theorem tailTrace_1153690 : CollatzResearch.WordTrace tailWord_1153690 prefixEnd_1153690 131643888063488092504285 := by
  unfold tailWord_1153690
  simp only [CollatzResearch.WordTrace]
  refine ⟨10519632797596409852596631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28052354126923759606924349 10519632797596409852596631)
  ·
    refine ⟨15779449196394614778894947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10519632797596409852596631 15779449196394614778894947)
    ·
      refine ⟨23669173794591922168342421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15779449196394614778894947 23669173794591922168342421)
      ·
        refine ⟨1109492521621496351641051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23669173794591922168342421 1109492521621496351641051)
        ·
          refine ⟨1664238782432244527461577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109492521621496351641051 1664238782432244527461577)
          ·
            refine ⟨1248179086824183395596183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1664238782432244527461577 1248179086824183395596183)
            ·
              refine ⟨1872268630236275093394275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1248179086824183395596183 1872268630236275093394275)
              ·
                refine ⟨2808402945354412640091413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1872268630236275093394275 2808402945354412640091413)
                ·
                  refine ⟨131643888063488092504285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2808402945354412640091413 131643888063488092504285)
                  ·
                    rfl

theorem cell22_1153690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_1153690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153690 prefixEnd_1153690 := by exact prefixLift 1153690
  have htrace : WordTrace (prefixWord ++ tailWord_1153690) baseStart_1153690 baseEnd_1153690 := by
    simpa [prefixWord, tailWord_1153690, baseEnd_1153690] using wordTrace_append hprefix tailTrace_1153690
  have hstable : (prefixWord ++ tailWord_1153690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153690).length < 2 ^ (prefixWord ++ tailWord_1153690).sum := by decide
  have hdescent : baseEnd_1153690 < baseStart_1153690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153699 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 2, 7]
def baseStart_1153699 : Nat := 118140960795 + 1153699 * 2 ^ 59
def prefixEnd_1153699 : Nat := 4983230072969 + 3 ^ 40 * 1153699 * 2
def baseEnd_1153699 : Nat := 394934745074391254037827

theorem tailTrace_1153699 : CollatzResearch.WordTrace tailWord_1153699 prefixEnd_1153699 394934745074391254037827 := by
  unfold tailWord_1153699
  simp only [CollatzResearch.WordTrace]
  refine ⟨42078859447353033947464151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28052572964902022631642767 42078859447353033947464151)
  ·
    refine ⟨63118289171029550921196227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42078859447353033947464151 63118289171029550921196227)
    ·
      refine ⟨94677433756544326381794341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63118289171029550921196227 94677433756544326381794341)
      ·
        refine ⟨17752018829352061196586439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94677433756544326381794341 17752018829352061196586439)
        ·
          refine ⟨26628028244028091794879659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17752018829352061196586439 26628028244028091794879659)
          ·
            refine ⟨39942042366042137692319489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26628028244028091794879659 39942042366042137692319489)
            ·
              refine ⟨29956531774531603269239617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39942042366042137692319489 29956531774531603269239617)
              ·
                refine ⟨22467398830898702451929713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29956531774531603269239617 22467398830898702451929713)
                ·
                  refine ⟨16850549123174026838947285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22467398830898702451929713 16850549123174026838947285)
                  ·
                    refine ⟨394934745074391254037827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16850549123174026838947285 394934745074391254037827)
                    ·
                      rfl

theorem cell22_1153699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 7].length) (baseStart_1153699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153699 prefixEnd_1153699 := by exact prefixLift 1153699
  have htrace : WordTrace (prefixWord ++ tailWord_1153699) baseStart_1153699 baseEnd_1153699 := by
    simpa [prefixWord, tailWord_1153699, baseEnd_1153699] using wordTrace_append hprefix tailTrace_1153699
  have hstable : (prefixWord ++ tailWord_1153699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153699).length < 2 ^ (prefixWord ++ tailWord_1153699).sum := by decide
  have hdescent : baseEnd_1153699 < baseStart_1153699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153741 : List Nat := [1, 6, 2, 1, 3, 1, 2, 2, 4]
def baseStart_1153741 : Nat := 118140960795 + 1153741 * 2 ^ 59
def prefixEnd_1153741 : Nat := 4983230072969 + 3 ^ 40 * 1153741 * 2
def baseEnd_1153741 : Nat := 131649707510905714829233

theorem tailTrace_1153741 : CollatzResearch.WordTrace tailWord_1153741 prefixEnd_1153741 131649707510905714829233 := by
  unfold tailWord_1153741
  simp only [CollatzResearch.WordTrace]
  refine ⟨42080391313200875120493077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28053594208800583413662051 42080391313200875120493077)
  ·
    refine ⟨1972518342806291021273113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42080391313200875120493077 1972518342806291021273113)
    ·
      refine ⟨1479388757104718265954835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1972518342806291021273113 1479388757104718265954835)
      ·
        refine ⟨2219083135657077398932253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1479388757104718265954835 2219083135657077398932253)
        ·
          refine ⟨832156175871404024599595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2219083135657077398932253 832156175871404024599595)
          ·
            refine ⟨1248234263807106036899393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832156175871404024599595 1248234263807106036899393)
            ·
              refine ⟨936175697855329527674545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1248234263807106036899393 936175697855329527674545)
              ·
                refine ⟨702131773391497145755909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 936175697855329527674545 702131773391497145755909)
                ·
                  refine ⟨131649707510905714829233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 702131773391497145755909 131649707510905714829233)
                  ·
                    rfl

theorem cell22_1153741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_1153741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153741 prefixEnd_1153741 := by exact prefixLift 1153741
  have htrace : WordTrace (prefixWord ++ tailWord_1153741) baseStart_1153741 baseEnd_1153741 := by
    simpa [prefixWord, tailWord_1153741, baseEnd_1153741] using wordTrace_append hprefix tailTrace_1153741
  have hstable : (prefixWord ++ tailWord_1153741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153741).length < 2 ^ (prefixWord ++ tailWord_1153741).sum := by decide
  have hdescent : baseEnd_1153741 < baseStart_1153741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153761 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 1, 7]
def baseStart_1153761 : Nat := 118140960795 + 1153761 * 2 ^ 59
def prefixEnd_1153761 : Nat := 4983230072969 + 3 ^ 40 * 1153761 * 2
def baseEnd_1153761 : Nat := 394955968941443758987637

theorem tailTrace_1153761 : CollatzResearch.WordTrace tailWord_1153761 prefixEnd_1153761 394955968941443758987637 := by
  unfold tailWord_1153761
  simp only [CollatzResearch.WordTrace]
  refine ⟨42081120773128418536221137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28054080515418945690814091 42081120773128418536221137)
  ·
    refine ⟨31560840579846313902165853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42081120773128418536221137 31560840579846313902165853)
    ·
      refine ⟨11835315217442367713312195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31560840579846313902165853 11835315217442367713312195)
      ·
        refine ⟨17752972826163551569968293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11835315217442367713312195 17752972826163551569968293)
        ·
          refine ⟨3328682404905665919369055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17752972826163551569968293 3328682404905665919369055)
          ·
            refine ⟨4993023607358498879053583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3328682404905665919369055 4993023607358498879053583)
            ·
              refine ⟨7489535411037748318580375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4993023607358498879053583 7489535411037748318580375)
              ·
                refine ⟨11234303116556622477870563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7489535411037748318580375 11234303116556622477870563)
                ·
                  refine ⟨16851454674834933716805845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11234303116556622477870563 16851454674834933716805845)
                  ·
                    refine ⟨394955968941443758987637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16851454674834933716805845 394955968941443758987637)
                    ·
                      rfl

theorem cell22_1153761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_1153761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153761 prefixEnd_1153761 := by exact prefixLift 1153761
  have htrace : WordTrace (prefixWord ++ tailWord_1153761) baseStart_1153761 baseEnd_1153761 := by
    simpa [prefixWord, tailWord_1153761, baseEnd_1153761] using wordTrace_append hprefix tailTrace_1153761
  have hstable : (prefixWord ++ tailWord_1153761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153761).length < 2 ^ (prefixWord ++ tailWord_1153761).sum := by decide
  have hdescent : baseEnd_1153761 < baseStart_1153761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153763 : List Nat := [1, 1, 1, 7, 1, 1, 2, 3, 5]
def baseStart_1153763 : Nat := 118140960795 + 1153763 * 2 ^ 59
def prefixEnd_1153763 : Nat := 4983230072969 + 3 ^ 40 * 1153763 * 2
def baseEnd_1153763 : Nat := 131652217860772140145877

theorem tailTrace_1153763 : CollatzResearch.WordTrace tailWord_1153763 prefixEnd_1153763 131652217860772140145877 := by
  unfold tailWord_1153763
  simp only [CollatzResearch.WordTrace]
  refine ⟨42081193719121172877793943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28054129146080781918529295 42081193719121172877793943)
  ·
    refine ⟨63121790578681759316690915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42081193719121172877793943 63121790578681759316690915)
    ·
      refine ⟨94682685868022638975036373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63121790578681759316690915 94682685868022638975036373)
      ·
        refine ⟨2219125450031780600977415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 94682685868022638975036373 2219125450031780600977415)
        ·
          refine ⟨3328688175047670901466123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2219125450031780600977415 3328688175047670901466123)
          ·
            refine ⟨4993032262571506352199185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3328688175047670901466123 4993032262571506352199185)
            ·
              refine ⟨3744774196928629764149389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4993032262571506352199185 3744774196928629764149389)
              ·
                refine ⟨1404290323848236161556021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3744774196928629764149389 1404290323848236161556021)
                ·
                  refine ⟨131652217860772140145877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1404290323848236161556021 131652217860772140145877)
                  ·
                    rfl

theorem cell22_1153763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 5].length) (baseStart_1153763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153763 prefixEnd_1153763 := by exact prefixLift 1153763
  have htrace : WordTrace (prefixWord ++ tailWord_1153763) baseStart_1153763 baseEnd_1153763 := by
    simpa [prefixWord, tailWord_1153763, baseEnd_1153763] using wordTrace_append hprefix tailTrace_1153763
  have hstable : (prefixWord ++ tailWord_1153763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153763).length < 2 ^ (prefixWord ++ tailWord_1153763).sum := by decide
  have hdescent : baseEnd_1153763 < baseStart_1153763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153776 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 3, 4]
def baseStart_1153776 : Nat := 118140960795 + 1153776 * 2 ^ 59
def prefixEnd_1153776 : Nat := 4983230072969 + 3 ^ 40 * 1153776 * 2
def baseEnd_1153776 : Nat := 394961103747988719862591

theorem tailTrace_1153776 : CollatzResearch.WordTrace tailWord_1153776 prefixEnd_1153776 394961103747988719862591 := by
  unfold tailWord_1153776
  simp only [CollatzResearch.WordTrace]
  refine ⟨21040833934037038049008591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28054445245382717398678121 21040833934037038049008591)
  ·
    refine ⟨31561250901055557073512887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21040833934037038049008591 31561250901055557073512887)
    ·
      refine ⟨47341876351583335610269331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31561250901055557073512887 47341876351583335610269331)
      ·
        refine ⟨71012814527375003415403997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47341876351583335610269331 71012814527375003415403997)
        ·
          refine ⟨26629805447765626280776499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71012814527375003415403997 26629805447765626280776499)
          ·
            refine ⟨39944708171648439421164749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26629805447765626280776499 39944708171648439421164749)
            ·
              refine ⟨14979265564368164782936781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39944708171648439421164749 14979265564368164782936781)
              ·
                refine ⟨5617224586638061793601293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14979265564368164782936781 5617224586638061793601293)
                ·
                  refine ⟨2106459219989273172600485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5617224586638061793601293 2106459219989273172600485)
                  ·
                    refine ⟨394961103747988719862591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2106459219989273172600485 394961103747988719862591)
                    ·
                      rfl

theorem cell22_1153776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 3, 4].length) (baseStart_1153776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153776 prefixEnd_1153776 := by exact prefixLift 1153776
  have htrace : WordTrace (prefixWord ++ tailWord_1153776) baseStart_1153776 baseEnd_1153776 := by
    simpa [prefixWord, tailWord_1153776, baseEnd_1153776] using wordTrace_append hprefix tailTrace_1153776
  have hstable : (prefixWord ++ tailWord_1153776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153776).length < 2 ^ (prefixWord ++ tailWord_1153776).sum := by decide
  have hdescent : baseEnd_1153776 < baseStart_1153776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153823 : List Nat := [1, 1, 2, 4, 2, 2, 3, 1, 1, 5]
def baseStart_1153823 : Nat := 118140960795 + 1153823 * 2 ^ 59
def prefixEnd_1153823 : Nat := 4983230072969 + 3 ^ 40 * 1153823 * 2
def baseEnd_1153823 : Nat := 394977192808496263937447

theorem tailTrace_1153823 : CollatzResearch.WordTrace tailWord_1153823 prefixEnd_1153823 394977192808496263937447 := by
  unfold tailWord_1153823
  simp only [CollatzResearch.WordTrace]
  refine ⟨42083382098903803124978123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28055588065935868749985415 42083382098903803124978123)
  ·
    refine ⟨63125073148355704687467185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42083382098903803124978123 63125073148355704687467185)
    ·
      refine ⟨47343804861266778515600389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63125073148355704687467185 47343804861266778515600389)
      ·
        refine ⟨8876963411487520971675073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47343804861266778515600389 8876963411487520971675073)
        ·
          refine ⟨6657722558615640728756305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8876963411487520971675073 6657722558615640728756305)
          ·
            refine ⟨4993291918961730546567229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6657722558615640728756305 4993291918961730546567229)
            ·
              refine ⟨1872484469610648954962711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4993291918961730546567229 1872484469610648954962711)
              ·
                refine ⟨2808726704415973432444067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1872484469610648954962711 2808726704415973432444067)
                ·
                  refine ⟨4213090056623960148666101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2808726704415973432444067 4213090056623960148666101)
                  ·
                    refine ⟨394977192808496263937447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4213090056623960148666101 394977192808496263937447)
                    ·
                      rfl

theorem cell22_1153823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 5].length) (baseStart_1153823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153823 prefixEnd_1153823 := by exact prefixLift 1153823
  have htrace : WordTrace (prefixWord ++ tailWord_1153823) baseStart_1153823 baseEnd_1153823 := by
    simpa [prefixWord, tailWord_1153823, baseEnd_1153823] using wordTrace_append hprefix tailTrace_1153823
  have hstable : (prefixWord ++ tailWord_1153823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153823).length < 2 ^ (prefixWord ++ tailWord_1153823).sum := by decide
  have hdescent : baseEnd_1153823 < baseStart_1153823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153836 : List Nat := [2, 2, 1, 1, 1, 4, 3, 8]
def baseStart_1153836 : Nat := 118140960795 + 1153836 * 2 ^ 59
def prefixEnd_1153836 : Nat := 4983230072969 + 3 ^ 40 * 1153836 * 2
def baseEnd_1153836 : Nat := 43886849219352062595823

theorem tailTrace_1153836 : CollatzResearch.WordTrace tailWord_1153836 prefixEnd_1153836 43886849219352062595823 := by
  unfold tailWord_1153836
  simp only [CollatzResearch.WordTrace]
  refine ⟨21041928123928353172600681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28055904165237804230134241 21041928123928353172600681)
  ·
    refine ⟨15781446092946264879450511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21041928123928353172600681 15781446092946264879450511)
    ·
      refine ⟨23672169139419397319175767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15781446092946264879450511 23672169139419397319175767)
      ·
        refine ⟨35508253709129095978763651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23672169139419397319175767 35508253709129095978763651)
        ·
          refine ⟨53262380563693643968145477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35508253709129095978763651 53262380563693643968145477)
          ·
            refine ⟨9986696355692558244027277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53262380563693643968145477 9986696355692558244027277)
            ·
              refine ⟨3745011133384709341510229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9986696355692558244027277 3745011133384709341510229)
              ·
                refine ⟨43886849219352062595823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3745011133384709341510229 43886849219352062595823)
                ·
                  rfl

theorem cell22_1153836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 8].length) (baseStart_1153836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153836 prefixEnd_1153836 := by exact prefixLift 1153836
  have htrace : WordTrace (prefixWord ++ tailWord_1153836) baseStart_1153836 baseEnd_1153836 := by
    simpa [prefixWord, tailWord_1153836, baseEnd_1153836] using wordTrace_append hprefix tailTrace_1153836
  have hstable : (prefixWord ++ tailWord_1153836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153836).length < 2 ^ (prefixWord ++ tailWord_1153836).sum := by decide
  have hdescent : baseEnd_1153836 < baseStart_1153836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153930 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 2, 5]
def baseStart_1153930 : Nat := 118140960795 + 1153930 * 2 ^ 59
def prefixEnd_1153930 : Nat := 4983230072969 + 3 ^ 40 * 1153930 * 2
def baseEnd_1153930 : Nat := 395013821095183651512119

theorem tailTrace_1153930 : CollatzResearch.WordTrace tailWord_1153930 prefixEnd_1153930 395013821095183651512119 := by
  unfold tailWord_1153930
  simp only [CollatzResearch.WordTrace]
  refine ⟨10521821177379040099780811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28058189806344106932748829 10521821177379040099780811)
  ·
    refine ⟨15782731766068560149671217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10521821177379040099780811 15782731766068560149671217)
    ·
      refine ⟨11837048824551420112253413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15782731766068560149671217 11837048824551420112253413)
      ·
        refine ⟨2219446654603391271047515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11837048824551420112253413 2219446654603391271047515)
        ·
          refine ⟨3329169981905086906571273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2219446654603391271047515 3329169981905086906571273)
          ·
            refine ⟨2496877486428815179928455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3329169981905086906571273 2496877486428815179928455)
            ·
              refine ⟨3745316229643222769892683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2496877486428815179928455 3745316229643222769892683)
              ·
                refine ⟨5617974344464834154839025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3745316229643222769892683 5617974344464834154839025)
                ·
                  refine ⟨4213480758348625616129269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5617974344464834154839025 4213480758348625616129269)
                  ·
                    refine ⟨395013821095183651512119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4213480758348625616129269 395013821095183651512119)
                    ·
                      rfl

theorem cell22_1153930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_1153930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153930 prefixEnd_1153930 := by exact prefixLift 1153930
  have htrace : WordTrace (prefixWord ++ tailWord_1153930) baseStart_1153930 baseEnd_1153930 := by
    simpa [prefixWord, tailWord_1153930, baseEnd_1153930] using wordTrace_append hprefix tailTrace_1153930
  have hstable : (prefixWord ++ tailWord_1153930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153930).length < 2 ^ (prefixWord ++ tailWord_1153930).sum := by decide
  have hdescent : baseEnd_1153930 < baseStart_1153930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153943 : List Nat := [1, 1, 3, 3, 1, 2, 3, 2, 6]
def baseStart_1153943 : Nat := 118140960795 + 1153943 * 2 ^ 59
def prefixEnd_1153943 : Nat := 4983230072969 + 3 ^ 40 * 1153943 * 2
def baseEnd_1153943 : Nat := 131672757086951983645693

theorem tailTrace_1153943 : CollatzResearch.WordTrace tailWord_1153943 prefixEnd_1153943 131672757086951983645693 := by
  unfold tailWord_1153943
  simp only [CollatzResearch.WordTrace]
  refine ⟨42087758858469063619346483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28058505905646042412897655 42087758858469063619346483)
  ·
    refine ⟨63131638287703595429019725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42087758858469063619346483 63131638287703595429019725)
    ·
      refine ⟨23674364357888848285882397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63131638287703595429019725 23674364357888848285882397)
      ·
        refine ⟨8877886634208318107205899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23674364357888848285882397 8877886634208318107205899)
        ·
          refine ⟨13316829951312477160808849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8877886634208318107205899 13316829951312477160808849)
          ·
            refine ⟨9987622463484357870606637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13316829951312477160808849 9987622463484357870606637)
            ·
              refine ⟨3745358423806634201477489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9987622463484357870606637 3745358423806634201477489)
              ·
                refine ⟨2809018817854975651108117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3745358423806634201477489 2809018817854975651108117)
                ·
                  refine ⟨131672757086951983645693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2809018817854975651108117 131672757086951983645693)
                  ·
                    rfl

theorem cell22_1153943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 6].length) (baseStart_1153943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153943 prefixEnd_1153943 := by exact prefixLift 1153943
  have htrace : WordTrace (prefixWord ++ tailWord_1153943) baseStart_1153943 baseEnd_1153943 := by
    simpa [prefixWord, tailWord_1153943, baseEnd_1153943] using wordTrace_append hprefix tailTrace_1153943
  have hstable : (prefixWord ++ tailWord_1153943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153943).length < 2 ^ (prefixWord ++ tailWord_1153943).sum := by decide
  have hdescent : baseEnd_1153943 < baseStart_1153943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153992 : List Nat := [2, 1, 3, 1, 5, 2, 1, 1, 1, 5]
def baseStart_1153992 : Nat := 118140960795 + 1153992 * 2 ^ 59
def prefixEnd_1153992 : Nat := 4983230072969 + 3 ^ 40 * 1153992 * 2
def baseEnd_1153992 : Nat := 395035044962236156461929

theorem tailTrace_1153992 : CollatzResearch.WordTrace tailWord_1153992 prefixEnd_1153992 395035044962236156461929 := by
  unfold tailWord_1153992
  simp only [CollatzResearch.WordTrace]
  refine ⟨21044773017645772493940115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28059697356861029991920153 21044773017645772493940115)
  ·
    refine ⟨31567159526468658740910173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21044773017645772493940115 31567159526468658740910173)
    ·
      refine ⟨11837684822425747027841315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31567159526468658740910173 11837684822425747027841315)
      ·
        refine ⟨17756527233638620541761973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11837684822425747027841315 17756527233638620541761973)
        ·
          refine ⟨1664674428153620675790185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17756527233638620541761973 1664674428153620675790185)
          ·
            refine ⟨1248505821115215506842639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1664674428153620675790185 1248505821115215506842639)
            ·
              refine ⟨1872758731672823260263959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1248505821115215506842639 1872758731672823260263959)
              ·
                refine ⟨2809138097509234890395939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1872758731672823260263959 2809138097509234890395939)
                ·
                  refine ⟨4213707146263852335593909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2809138097509234890395939 4213707146263852335593909)
                  ·
                    refine ⟨395035044962236156461929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4213707146263852335593909 395035044962236156461929)
                    ·
                      rfl

theorem cell22_1153992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_1153992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1153992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1153992 prefixEnd_1153992 := by exact prefixLift 1153992
  have htrace : WordTrace (prefixWord ++ tailWord_1153992) baseStart_1153992 baseEnd_1153992 := by
    simpa [prefixWord, tailWord_1153992, baseEnd_1153992] using wordTrace_append hprefix tailTrace_1153992
  have hstable : (prefixWord ++ tailWord_1153992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153992).length < 2 ^ (prefixWord ++ tailWord_1153992).sum := by decide
  have hdescent : baseEnd_1153992 < baseStart_1153992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154005 : List Nat := [1, 3, 2, 3, 3, 1, 1, 8]
def baseStart_1154005 : Nat := 118140960795 + 1154005 * 2 ^ 59
def prefixEnd_1154005 : Nat := 4983230072969 + 3 ^ 40 * 1154005 * 2
def baseEnd_1154005 : Nat := 43893277236434272876321

theorem tailTrace_1154005 : CollatzResearch.WordTrace tailWord_1154005 prefixEnd_1154005 43893277236434272876321 := by
  unfold tailWord_1154005
  simp only [CollatzResearch.WordTrace]
  refine ⟨42090020184244448208103469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28060013456162965472068979 42090020184244448208103469)
  ·
    refine ⟨15783757569091668078038801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42090020184244448208103469 15783757569091668078038801)
    ·
      refine ⟨11837818176818751058529101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15783757569091668078038801 11837818176818751058529101)
      ·
        refine ⟨4439181816307031646948413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11837818176818751058529101 4439181816307031646948413)
        ·
          refine ⟨1664693181115136867605655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4439181816307031646948413 1664693181115136867605655)
          ·
            refine ⟨2497039771672705301408483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1664693181115136867605655 2497039771672705301408483)
            ·
              refine ⟨3745559657509057952112725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2497039771672705301408483 3745559657509057952112725)
              ·
                refine ⟨43893277236434272876321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3745559657509057952112725 43893277236434272876321)
                ·
                  rfl

theorem cell22_1154005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 8].length) (baseStart_1154005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154005 prefixEnd_1154005 := by exact prefixLift 1154005
  have htrace : WordTrace (prefixWord ++ tailWord_1154005) baseStart_1154005 baseEnd_1154005 := by
    simpa [prefixWord, tailWord_1154005, baseEnd_1154005] using wordTrace_append hprefix tailTrace_1154005
  have hstable : (prefixWord ++ tailWord_1154005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154005).length < 2 ^ (prefixWord ++ tailWord_1154005).sum := by decide
  have hdescent : baseEnd_1154005 < baseStart_1154005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154048 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 6, 5]
def baseStart_1154048 : Nat := 118140960795 + 1154048 * 2 ^ 59
def prefixEnd_1154048 : Nat := 4983230072969 + 3 ^ 40 * 1154048 * 2
def baseEnd_1154048 : Nat := 395054214906670677061757

theorem tailTrace_1154048 : CollatzResearch.WordTrace tailWord_1154048 prefixEnd_1154048 395054214906670677061757 := by
  unfold tailWord_1154048
  simp only [CollatzResearch.WordTrace]
  refine ⟨21045794261544333275959399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28061059015392444367945865 21045794261544333275959399)
  ·
    refine ⟨31568691392316499913939099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21045794261544333275959399 31568691392316499913939099)
    ·
      refine ⟨47353037088474749870908649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31568691392316499913939099 47353037088474749870908649)
      ·
        refine ⟨35514777816356062403181487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47353037088474749870908649 35514777816356062403181487)
        ·
          refine ⟨53272166724534093604772231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35514777816356062403181487 53272166724534093604772231)
          ·
            refine ⟨79908250086801140407158347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53272166724534093604772231 79908250086801140407158347)
            ·
              refine ⟨119862375130201710610737521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79908250086801140407158347 119862375130201710610737521)
              ·
                refine ⟨89896781347651282958053141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119862375130201710610737521 89896781347651282958053141)
                ·
                  refine ⟨4213911625671153888658741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89896781347651282958053141 4213911625671153888658741)
                  ·
                    refine ⟨395054214906670677061757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4213911625671153888658741 395054214906670677061757)
                    ·
                      rfl

theorem cell22_1154048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_1154048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154048 prefixEnd_1154048 := by exact prefixLift 1154048
  have htrace : WordTrace (prefixWord ++ tailWord_1154048) baseStart_1154048 baseEnd_1154048 := by
    simpa [prefixWord, tailWord_1154048, baseEnd_1154048] using wordTrace_append hprefix tailTrace_1154048
  have hstable : (prefixWord ++ tailWord_1154048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154048).length < 2 ^ (prefixWord ++ tailWord_1154048).sum := by decide
  have hdescent : baseEnd_1154048 < baseStart_1154048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154140 : List Nat := [2, 2, 4, 1, 1, 1, 11]
def baseStart_1154140 : Nat := 118140960795 + 1154140 * 2 ^ 59
def prefixEnd_1154140 : Nat := 4983230072969 + 3 ^ 40 * 1154140 * 2
def baseEnd_1154140 : Nat := 14632804014326411250425

theorem tailTrace_1154140 : CollatzResearch.WordTrace tailWord_1154140 prefixEnd_1154140 14632804014326411250425 := by
  unfold tailWord_1154140
  simp only [CollatzResearch.WordTrace]
  refine ⟨21047472019377683132133937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28063296025836910842845249 21047472019377683132133937)
  ·
    refine ⟨15785604014533262349100453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21047472019377683132133937 15785604014533262349100453)
    ·
      refine ⟨2959800752724986690456335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15785604014533262349100453 2959800752724986690456335)
      ·
        refine ⟨4439701129087480035684503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2959800752724986690456335 4439701129087480035684503)
        ·
          refine ⟨6659551693631220053526755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4439701129087480035684503 6659551693631220053526755)
          ·
            refine ⟨9989327540446830080290133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6659551693631220053526755 9989327540446830080290133)
            ·
              refine ⟨14632804014326411250425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9989327540446830080290133 14632804014326411250425)
              ·
                rfl

theorem cell22_1154140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 11].length) (baseStart_1154140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154140 prefixEnd_1154140 := by exact prefixLift 1154140
  have htrace : WordTrace (prefixWord ++ tailWord_1154140) baseStart_1154140 baseEnd_1154140 := by
    simpa [prefixWord, tailWord_1154140, baseEnd_1154140] using wordTrace_append hprefix tailTrace_1154140
  have hstable : (prefixWord ++ tailWord_1154140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154140).length < 2 ^ (prefixWord ++ tailWord_1154140).sum := by decide
  have hdescent : baseEnd_1154140 < baseStart_1154140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154172 : List Nat := [2, 2, 2, 1, 1, 3, 1, 4, 3, 3]
def baseStart_1154172 : Nat := 118140960795 + 1154172 * 2 ^ 59
def prefixEnd_1154172 : Nat := 4983230072969 + 3 ^ 40 * 1154172 * 2
def baseEnd_1154172 : Nat := 395096662640775686961377

theorem tailTrace_1154172 : CollatzResearch.WordTrace tailWord_1154172 prefixEnd_1154172 395096662640775686961377 := by
  unfold tailWord_1154172
  simp only [CollatzResearch.WordTrace]
  refine ⟨21048055587319717864716385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28064074116426290486288513 21048055587319717864716385)
  ·
    refine ⟨15786041690489788398537289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21048055587319717864716385 15786041690489788398537289)
    ·
      refine ⟨11839531267867341298902967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15786041690489788398537289 11839531267867341298902967)
      ·
        refine ⟨17759296901801011948354451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11839531267867341298902967 17759296901801011948354451)
        ·
          refine ⟨26638945352701517922531677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17759296901801011948354451 26638945352701517922531677)
          ·
            refine ⟨9989604507263069220949379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26638945352701517922531677 9989604507263069220949379)
            ·
              refine ⟨14984406760894603831424069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9989604507263069220949379 14984406760894603831424069)
              ·
                refine ⟨2809576267667738218392013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14984406760894603831424069 2809576267667738218392013)
                ·
                  refine ⟨1053591100375401831897005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2809576267667738218392013 1053591100375401831897005)
                  ·
                    refine ⟨395096662640775686961377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1053591100375401831897005 395096662640775686961377)
                    ·
                      rfl

theorem cell22_1154172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_1154172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154172 prefixEnd_1154172 := by exact prefixLift 1154172
  have htrace : WordTrace (prefixWord ++ tailWord_1154172) baseStart_1154172 baseEnd_1154172 := by
    simpa [prefixWord, tailWord_1154172, baseEnd_1154172] using wordTrace_append hprefix tailTrace_1154172
  have hstable : (prefixWord ++ tailWord_1154172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154172).length < 2 ^ (prefixWord ++ tailWord_1154172).sum := by decide
  have hdescent : baseEnd_1154172 < baseStart_1154172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154185 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 7]
def baseStart_1154185 : Nat := 118140960795 + 1154185 * 2 ^ 59
def prefixEnd_1154185 : Nat := 4983230072969 + 3 ^ 40 * 1154185 * 2
def baseEnd_1154185 : Nat := 131700370935482662128779

theorem tailTrace_1154185 : CollatzResearch.WordTrace tailWord_1154185 prefixEnd_1154185 131700370935482662128779 := by
  unfold tailWord_1154185
  simp only [CollatzResearch.WordTrace]
  refine ⟨42096585323592338949656009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28064390215728225966437339 42096585323592338949656009)
  ·
    refine ⟨31572438992694254212242007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42096585323592338949656009 31572438992694254212242007)
    ·
      refine ⟨47358658489041381318363011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31572438992694254212242007 47358658489041381318363011)
      ·
        refine ⟨71037987733562071977544517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47358658489041381318363011 71037987733562071977544517)
        ·
          refine ⟨13319622700042888495789597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71037987733562071977544517 13319622700042888495789597)
          ·
            refine ⟨4994858512516083185921099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13319622700042888495789597 4994858512516083185921099)
            ·
              refine ⟨7492287768774124778881649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4994858512516083185921099 7492287768774124778881649)
              ·
                refine ⟨5619215826580593584161237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7492287768774124778881649 5619215826580593584161237)
                ·
                  refine ⟨131700370935482662128779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5619215826580593584161237 131700370935482662128779)
                  ·
                    rfl

theorem cell22_1154185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 7].length) (baseStart_1154185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154185 prefixEnd_1154185 := by exact prefixLift 1154185
  have htrace : WordTrace (prefixWord ++ tailWord_1154185) baseStart_1154185 baseEnd_1154185 := by
    simpa [prefixWord, tailWord_1154185, baseEnd_1154185] using wordTrace_append hprefix tailTrace_1154185
  have hstable : (prefixWord ++ tailWord_1154185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154185).length < 2 ^ (prefixWord ++ tailWord_1154185).sum := by decide
  have hdescent : baseEnd_1154185 < baseStart_1154185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154202 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 7]
def baseStart_1154202 : Nat := 118140960795 + 1154202 * 2 ^ 59
def prefixEnd_1154202 : Nat := 4983230072969 + 3 ^ 40 * 1154202 * 2
def baseEnd_1154202 : Nat := 131702310751288536237095

theorem tailTrace_1154202 : CollatzResearch.WordTrace tailWord_1154202 prefixEnd_1154202 131702310751288536237095 := by
  unfold tailWord_1154202
  simp only [CollatzResearch.WordTrace]
  refine ⟨10524301341132687713256215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28064803576353833902016573 10524301341132687713256215)
  ·
    refine ⟨15786452011699031569884323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10524301341132687713256215 15786452011699031569884323)
    ·
      refine ⟨23679678017548547354826485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15786452011699031569884323 23679678017548547354826485)
      ·
        refine ⟨2219969814145176314514983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23679678017548547354826485 2219969814145176314514983)
        ·
          refine ⟨3329954721217764471772475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2219969814145176314514983 3329954721217764471772475)
          ·
            refine ⟨4994932081826646707658713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3329954721217764471772475 4994932081826646707658713)
            ·
              refine ⟨3746199061369985030744035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4994932081826646707658713 3746199061369985030744035)
              ·
                refine ⟨5619298592054977546116053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3746199061369985030744035 5619298592054977546116053)
                ·
                  refine ⟨131702310751288536237095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5619298592054977546116053 131702310751288536237095)
                  ·
                    rfl

theorem cell22_1154202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_1154202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154202 prefixEnd_1154202 := by exact prefixLift 1154202
  have htrace : WordTrace (prefixWord ++ tailWord_1154202) baseStart_1154202 baseEnd_1154202 := by
    simpa [prefixWord, tailWord_1154202, baseEnd_1154202] using wordTrace_append hprefix tailTrace_1154202
  have hstable : (prefixWord ++ tailWord_1154202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154202).length < 2 ^ (prefixWord ++ tailWord_1154202).sum := by decide
  have hdescent : baseEnd_1154202 < baseStart_1154202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154206 : List Nat := [4, 3, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_1154206 : Nat := 118140960795 + 1154206 * 2 ^ 59
def prefixEnd_1154206 : Nat := 4983230072969 + 3 ^ 40 * 1154206 * 2
def baseEnd_1154206 : Nat := 395108301535610931611273

theorem tailTrace_1154206 : CollatzResearch.WordTrace tailWord_1154206 prefixEnd_1154206 395108301535610931611273 := by
  unfold tailWord_1154206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5262168907064532442021309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28064900837677506357446981 5262168907064532442021309)
  ·
    refine ⟨1973313340149199665757991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5262168907064532442021309 1973313340149199665757991)
    ·
      refine ⟨2959970010223799498636987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1973313340149199665757991 2959970010223799498636987)
      ·
        refine ⟨4439955015335699247955481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2959970010223799498636987 4439955015335699247955481)
        ·
          refine ⟨3329966261501774435966611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4439955015335699247955481 3329966261501774435966611)
          ·
            refine ⟨4994949392252661653949917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3329966261501774435966611 4994949392252661653949917)
            ·
              refine ⟨1873106022094748120231219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4994949392252661653949917 1873106022094748120231219)
              ·
                refine ⟨2809659033142122180346829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1873106022094748120231219 2809659033142122180346829)
                ·
                  refine ⟨1053622137428295817630061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2809659033142122180346829 1053622137428295817630061)
                  ·
                    refine ⟨395108301535610931611273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1053622137428295817630061 395108301535610931611273)
                    ·
                      rfl

theorem cell22_1154206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_1154206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154206 prefixEnd_1154206 := by exact prefixLift 1154206
  have htrace : WordTrace (prefixWord ++ tailWord_1154206) baseStart_1154206 baseEnd_1154206 := by
    simpa [prefixWord, tailWord_1154206, baseEnd_1154206] using wordTrace_append hprefix tailTrace_1154206
  have hstable : (prefixWord ++ tailWord_1154206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154206).length < 2 ^ (prefixWord ++ tailWord_1154206).sum := by decide
  have hdescent : baseEnd_1154206 < baseStart_1154206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154232 : List Nat := [2, 1, 2, 1, 2, 1, 2, 6, 1, 4]
def baseStart_1154232 : Nat := 118140960795 + 1154232 * 2 ^ 59
def prefixEnd_1154232 : Nat := 4983230072969 + 3 ^ 40 * 1154232 * 2
def baseEnd_1154232 : Nat := 395117201866955530461193

theorem tailTrace_1154232 : CollatzResearch.WordTrace tailWord_1154232 prefixEnd_1154232 395117201866955530461193 := by
  unfold tailWord_1154232
  simp only [CollatzResearch.WordTrace]
  refine ⟨21049149777211032988308475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28065533036281377317744633 21049149777211032988308475)
  ·
    refine ⟨31573724665816549482462713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21049149777211032988308475 31573724665816549482462713)
    ·
      refine ⟨23680293499362412111847035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31573724665816549482462713 23680293499362412111847035)
      ·
        refine ⟨35520440249043618167770553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23680293499362412111847035 35520440249043618167770553)
        ·
          refine ⟨26640330186782713625827915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35520440249043618167770553 26640330186782713625827915)
          ·
            refine ⟨39960495280174070438741873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26640330186782713625827915 39960495280174070438741873)
            ·
              refine ⟨29970371460130552829056405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39960495280174070438741873 29970371460130552829056405)
              ·
                refine ⟨1404861162193619663862019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29970371460130552829056405 1404861162193619663862019)
                ·
                  refine ⟨2107291743290429495793029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1404861162193619663862019 2107291743290429495793029)
                  ·
                    refine ⟨395117201866955530461193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2107291743290429495793029 395117201866955530461193)
                    ·
                      rfl

theorem cell22_1154232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_1154232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154232 prefixEnd_1154232 := by exact prefixLift 1154232
  have htrace : WordTrace (prefixWord ++ tailWord_1154232) baseStart_1154232 baseEnd_1154232 := by
    simpa [prefixWord, tailWord_1154232, baseEnd_1154232] using wordTrace_append hprefix tailTrace_1154232
  have hstable : (prefixWord ++ tailWord_1154232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154232).length < 2 ^ (prefixWord ++ tailWord_1154232).sum := by decide
  have hdescent : baseEnd_1154232 < baseStart_1154232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154253 : List Nat := [1, 6, 2, 2, 1, 1, 2, 2, 5]
def baseStart_1154253 : Nat := 118140960795 + 1154253 * 2 ^ 59
def prefixEnd_1154253 : Nat := 4983230072969 + 3 ^ 40 * 1154253 * 2
def baseEnd_1154253 : Nat := 131708130198706158562043

theorem tailTrace_1154253 : CollatzResearch.WordTrace tailWord_1154253 prefixEnd_1154253 131708130198706158562043 := by
  unfold tailWord_1154253
  simp only [CollatzResearch.WordTrace]
  refine ⟨42099065487345986563131413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28066043658230657708754275 42099065487345986563131413)
  ·
    refine ⟨1973393694719343120146785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42099065487345986563131413 1973393694719343120146785)
    ·
      refine ⟨1480045271039507340110089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1973393694719343120146785 1480045271039507340110089)
      ·
        refine ⟨1110033953279630505082567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1480045271039507340110089 1110033953279630505082567)
        ·
          refine ⟨1665050929919445757623851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1110033953279630505082567 1665050929919445757623851)
          ·
            refine ⟨2497576394879168636435777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1665050929919445757623851 2497576394879168636435777)
            ·
              refine ⟨1873182296159376477326833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2497576394879168636435777 1873182296159376477326833)
              ·
                refine ⟨1404886722119532357995125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1873182296159376477326833 1404886722119532357995125)
                ·
                  refine ⟨131708130198706158562043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1404886722119532357995125 131708130198706158562043)
                  ·
                    rfl

theorem cell22_1154253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_1154253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154253 prefixEnd_1154253 := by exact prefixLift 1154253
  have htrace : WordTrace (prefixWord ++ tailWord_1154253) baseStart_1154253 baseEnd_1154253 := by
    simpa [prefixWord, tailWord_1154253, baseEnd_1154253] using wordTrace_append hprefix tailTrace_1154253
  have hstable : (prefixWord ++ tailWord_1154253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154253).length < 2 ^ (prefixWord ++ tailWord_1154253).sum := by decide
  have hdescent : baseEnd_1154253 < baseStart_1154253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154429 : List Nat := [1, 4, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_1154429 : Nat := 118140960795 + 1154429 * 2 ^ 59
def prefixEnd_1154429 : Nat := 4983230072969 + 3 ^ 40 * 1154429 * 2
def baseEnd_1154429 : Nat := 395184638992912683285589

theorem tailTrace_1154429 : CollatzResearch.WordTrace tailWord_1154429 prefixEnd_1154429 395184638992912683285589 := by
  unfold tailWord_1154429
  simp only [CollatzResearch.WordTrace]
  refine ⟨42105484734708368621538341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28070323156472245747692227 42105484734708368621538341)
  ·
    refine ⟨7894778387757819116538439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42105484734708368621538341 7894778387757819116538439)
    ·
      refine ⟨11842167581636728674807659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7894778387757819116538439 11842167581636728674807659)
      ·
        refine ⟨17763251372455093012211489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11842167581636728674807659 17763251372455093012211489)
        ·
          refine ⟨13322438529341319759158617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17763251372455093012211489 13322438529341319759158617)
          ·
            refine ⟨9991828897005989819368963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13322438529341319759158617 9991828897005989819368963)
            ·
              refine ⟨14987743345508984729053445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9991828897005989819368963 14987743345508984729053445)
              ·
                refine ⟨2810201877282934636697521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14987743345508984729053445 2810201877282934636697521)
                ·
                  refine ⟨2107651407962200977523141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2810201877282934636697521 2107651407962200977523141)
                  ·
                    refine ⟨395184638992912683285589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2107651407962200977523141 395184638992912683285589)
                    ·
                      rfl

theorem cell22_1154429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_1154429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154429 prefixEnd_1154429 := by exact prefixLift 1154429
  have htrace : WordTrace (prefixWord ++ tailWord_1154429) baseStart_1154429 baseEnd_1154429 := by
    simpa [prefixWord, tailWord_1154429, baseEnd_1154429] using wordTrace_append hprefix tailTrace_1154429
  have hstable : (prefixWord ++ tailWord_1154429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154429).length < 2 ^ (prefixWord ++ tailWord_1154429).sum := by decide
  have hdescent : baseEnd_1154429 < baseStart_1154429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154433 : List Nat := [1, 2, 4, 3, 2, 1, 1, 4, 4]
def baseStart_1154433 : Nat := 118140960795 + 1154433 * 2 ^ 59
def prefixEnd_1154433 : Nat := 4983230072969 + 3 ^ 40 * 1154433 * 2
def baseEnd_1154433 : Nat := 131728669424886002061859

theorem tailTrace_1154433 : CollatzResearch.WordTrace tailWord_1154433 prefixEnd_1154433 131728669424886002061859 := by
  unfold tailWord_1154433
  simp only [CollatzResearch.WordTrace]
  refine ⟨42105630626693877304683953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28070420417795918203122635 42105630626693877304683953)
  ·
    refine ⟨31579222970020407978512965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42105630626693877304683953 31579222970020407978512965)
    ·
      refine ⟨5921104306878826495971181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31579222970020407978512965 5921104306878826495971181)
      ·
        refine ⟨2220414115079559935989193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5921104306878826495971181 2220414115079559935989193)
        ·
          refine ⟨1665310586309669951991895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2220414115079559935989193 1665310586309669951991895)
          ·
            refine ⟨2497965879464504927987843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1665310586309669951991895 2497965879464504927987843)
            ·
              refine ⟨3746948819196757391981765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2497965879464504927987843 3746948819196757391981765)
              ·
                refine ⟨702552903599392010996581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3746948819196757391981765 702552903599392010996581)
                ·
                  refine ⟨131728669424886002061859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 702552903599392010996581 131728669424886002061859)
                  ·
                    rfl

theorem cell22_1154433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 4].length) (baseStart_1154433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154433 prefixEnd_1154433 := by exact prefixLift 1154433
  have htrace : WordTrace (prefixWord ++ tailWord_1154433) baseStart_1154433 baseEnd_1154433 := by
    simpa [prefixWord, tailWord_1154433, baseEnd_1154433] using wordTrace_append hprefix tailTrace_1154433
  have hstable : (prefixWord ++ tailWord_1154433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154433).length < 2 ^ (prefixWord ++ tailWord_1154433).sum := by decide
  have hdescent : baseEnd_1154433 < baseStart_1154433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154461 : List Nat := [1, 4, 2, 1, 3, 2, 3, 6]
def baseStart_1154461 : Nat := 118140960795 + 1154461 * 2 ^ 59
def prefixEnd_1154461 : Nat := 4983230072969 + 3 ^ 40 * 1154461 * 2
def baseEnd_1154461 : Nat := 43910621471875029609499

theorem tailTrace_1154461 : CollatzResearch.WordTrace tailWord_1154461 prefixEnd_1154461 43910621471875029609499 := by
  unfold tailWord_1154461
  simp only [CollatzResearch.WordTrace]
  refine ⟨42106651870592438086703237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28071101247061625391135491 42106651870592438086703237)
  ·
    refine ⟨7894997225736082141256857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42106651870592438086703237 7894997225736082141256857)
    ·
      refine ⟨5921247919302061605942643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7894997225736082141256857 5921247919302061605942643)
      ·
        refine ⟨8881871878953092408913965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5921247919302061605942643 8881871878953092408913965)
        ·
          refine ⟨3330701954607409653342737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8881871878953092408913965 3330701954607409653342737)
          ·
            refine ⟨2498026465955557240007053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3330701954607409653342737 2498026465955557240007053)
            ·
              refine ⟨936759924733333965002645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2498026465955557240007053 936759924733333965002645)
              ·
                refine ⟨43910621471875029609499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 936759924733333965002645 43910621471875029609499)
                ·
                  rfl

theorem cell22_1154461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 6].length) (baseStart_1154461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154461 prefixEnd_1154461 := by exact prefixLift 1154461
  have htrace : WordTrace (prefixWord ++ tailWord_1154461) baseStart_1154461 baseEnd_1154461 := by
    simpa [prefixWord, tailWord_1154461, baseEnd_1154461] using wordTrace_append hprefix tailTrace_1154461
  have hstable : (prefixWord ++ tailWord_1154461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154461).length < 2 ^ (prefixWord ++ tailWord_1154461).sum := by decide
  have hdescent : baseEnd_1154461 < baseStart_1154461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154493 : List Nat := [1, 4, 1, 2, 2, 1, 1, 6, 1, 3]
def baseStart_1154493 : Nat := 118140960795 + 1154493 * 2 ^ 59
def prefixEnd_1154493 : Nat := 4983230072969 + 3 ^ 40 * 1154493 * 2
def baseEnd_1154493 : Nat := 395206547500837849685393

theorem tailTrace_1154493 : CollatzResearch.WordTrace tailWord_1154493 prefixEnd_1154493 395206547500837849685393 := by
  unfold tailWord_1154493
  simp only [CollatzResearch.WordTrace]
  refine ⟨42107819006476507551868133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28071879337651005034578755 42107819006476507551868133)
  ·
    refine ⟨7895216063714345165975275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42107819006476507551868133 7895216063714345165975275)
    ·
      refine ⟨11842824095571517748962913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7895216063714345165975275 11842824095571517748962913)
      ·
        refine ⟨8882118071678638311722185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11842824095571517748962913 8882118071678638311722185)
        ·
          refine ⟨6661588553758978733791639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8882118071678638311722185 6661588553758978733791639)
          ·
            refine ⟨9992382830638468100687459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6661588553758978733791639 9992382830638468100687459)
            ·
              refine ⟨14988574245957702151031189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9992382830638468100687459 14988574245957702151031189)
              ·
                refine ⟨702589417779267288329587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14988574245957702151031189 702589417779267288329587)
                ·
                  refine ⟨1053884126668900932494381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 702589417779267288329587 1053884126668900932494381)
                  ·
                    refine ⟨395206547500837849685393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1053884126668900932494381 395206547500837849685393)
                    ·
                      rfl

theorem cell22_1154493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_1154493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154493 prefixEnd_1154493 := by exact prefixLift 1154493
  have htrace : WordTrace (prefixWord ++ tailWord_1154493) baseStart_1154493 baseEnd_1154493 := by
    simpa [prefixWord, tailWord_1154493, baseEnd_1154493] using wordTrace_append hprefix tailTrace_1154493
  have hstable : (prefixWord ++ tailWord_1154493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154493).length < 2 ^ (prefixWord ++ tailWord_1154493).sum := by decide
  have hdescent : baseEnd_1154493 < baseStart_1154493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154504 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 2, 5]
def baseStart_1154504 : Nat := 118140960795 + 1154504 * 2 ^ 59
def prefixEnd_1154504 : Nat := 4983230072969 + 3 ^ 40 * 1154504 * 2
def baseEnd_1154504 : Nat := 395210313025637487660359

theorem tailTrace_1154504 : CollatzResearch.WordTrace tailWord_1154504 prefixEnd_1154504 395210313025637487660359 := by
  unfold tailWord_1154504
  simp only [CollatzResearch.WordTrace]
  refine ⟨21054110104718328215259283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28072146806291104287012377 21054110104718328215259283)
  ·
    refine ⟨31581165157077492322888925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21054110104718328215259283 31581165157077492322888925)
    ·
      refine ⟨11842936933904059621083347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31581165157077492322888925 11842936933904059621083347)
      ·
        refine ⟨17764405400856089431625021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11842936933904059621083347 17764405400856089431625021)
        ·
          refine ⟨6661652025321033536859383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17764405400856089431625021 6661652025321033536859383)
          ·
            refine ⟨9992478037981550305289075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6661652025321033536859383 9992478037981550305289075)
            ·
              refine ⟨14988717056972325457933613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9992478037981550305289075 14988717056972325457933613)
              ·
                refine ⟨5620768896364622046725105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14988717056972325457933613 5620768896364622046725105)
                ·
                  refine ⟨4215576672273466535043829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5620768896364622046725105 4215576672273466535043829)
                  ·
                    refine ⟨395210313025637487660359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4215576672273466535043829 395210313025637487660359)
                    ·
                      rfl

theorem cell22_1154504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_1154504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154504 prefixEnd_1154504 := by exact prefixLift 1154504
  have htrace : WordTrace (prefixWord ++ tailWord_1154504) baseStart_1154504 baseEnd_1154504 := by
    simpa [prefixWord, tailWord_1154504, baseEnd_1154504] using wordTrace_append hprefix tailTrace_1154504
  have hstable : (prefixWord ++ tailWord_1154504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154504).length < 2 ^ (prefixWord ++ tailWord_1154504).sum := by decide
  have hdescent : baseEnd_1154504 < baseStart_1154504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154519 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 3, 4]
def baseStart_1154519 : Nat := 118140960795 + 1154519 * 2 ^ 59
def prefixEnd_1154519 : Nat := 4983230072969 + 3 ^ 40 * 1154519 * 2
def baseEnd_1154519 : Nat := 395215447832182448535313

theorem tailTrace_1154519 : CollatzResearch.WordTrace tailWord_1154519 prefixEnd_1154519 395215447832182448535313 := by
  unfold tailWord_1154519
  simp only [CollatzResearch.WordTrace]
  refine ⟨42108767304382313992314611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28072511536254875994876407 42108767304382313992314611)
  ·
    refine ⟨63163150956573470988471917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42108767304382313992314611 63163150956573470988471917)
    ·
      refine ⟨23686181608715051620676969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63163150956573470988471917 23686181608715051620676969)
      ·
        refine ⟨17764636206536288715507727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23686181608715051620676969 17764636206536288715507727)
        ·
          refine ⟨26646954309804433073261591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17764636206536288715507727 26646954309804433073261591)
          ·
            refine ⟨39970431464706649609892387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26646954309804433073261591 39970431464706649609892387)
            ·
              refine ⟨59955647197059974414838581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39970431464706649609892387 59955647197059974414838581)
              ·
                refine ⟨5620841924724372601391117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59955647197059974414838581 5620841924724372601391117)
                ·
                  refine ⟨2107815721771639725521669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5620841924724372601391117 2107815721771639725521669)
                  ·
                    refine ⟨395215447832182448535313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2107815721771639725521669 395215447832182448535313)
                    ·
                      rfl

theorem cell22_1154519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_1154519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154519 prefixEnd_1154519 := by exact prefixLift 1154519
  have htrace : WordTrace (prefixWord ++ tailWord_1154519) baseStart_1154519 baseEnd_1154519 := by
    simpa [prefixWord, tailWord_1154519, baseEnd_1154519] using wordTrace_append hprefix tailTrace_1154519
  have hstable : (prefixWord ++ tailWord_1154519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154519).length < 2 ^ (prefixWord ++ tailWord_1154519).sum := by decide
  have hdescent : baseEnd_1154519 < baseStart_1154519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154536 : List Nat := [2, 1, 4, 1, 1, 2, 1, 5, 1, 4]
def baseStart_1154536 : Nat := 118140960795 + 1154536 * 2 ^ 59
def prefixEnd_1154536 : Nat := 4983230072969 + 3 ^ 40 * 1154536 * 2
def baseEnd_1154536 : Nat := 395221267279600070860261

theorem tailTrace_1154536 : CollatzResearch.WordTrace tailWord_1154536 prefixEnd_1154536 395221267279600070860261 := by
  unfold tailWord_1154536
  simp only [CollatzResearch.WordTrace]
  refine ⟨21054693672660362947841731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28072924896880483930455641 21054693672660362947841731)
  ·
    refine ⟨31582040508990544421762597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21054693672660362947841731 31582040508990544421762597)
    ·
      refine ⟨5921632595435727079080487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31582040508990544421762597 5921632595435727079080487)
      ·
        refine ⟨8882448893153590618620731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5921632595435727079080487 8882448893153590618620731)
        ·
          refine ⟨13323673339730385927931097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8882448893153590618620731 13323673339730385927931097)
          ·
            refine ⟨9992755004797789445948323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13323673339730385927931097 9992755004797789445948323)
            ·
              refine ⟨14989132507196684168922485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9992755004797789445948323 14989132507196684168922485)
              ·
                refine ⟨1405231172549689140836483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14989132507196684168922485 1405231172549689140836483)
                ·
                  refine ⟨2107846758824533711254725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1405231172549689140836483 2107846758824533711254725)
                  ·
                    refine ⟨395221267279600070860261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2107846758824533711254725 395221267279600070860261)
                    ·
                      rfl

theorem cell22_1154536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_1154536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154536 prefixEnd_1154536 := by exact prefixLift 1154536
  have htrace : WordTrace (prefixWord ++ tailWord_1154536) baseStart_1154536 baseEnd_1154536 := by
    simpa [prefixWord, tailWord_1154536, baseEnd_1154536] using wordTrace_append hprefix tailTrace_1154536
  have hstable : (prefixWord ++ tailWord_1154536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154536).length < 2 ^ (prefixWord ++ tailWord_1154536).sum := by decide
  have hdescent : baseEnd_1154536 < baseStart_1154536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154579 : List Nat := [1, 1, 1, 2, 1, 6, 2, 8]
def baseStart_1154579 : Nat := 118140960795 + 1154579 * 2 ^ 59
def prefixEnd_1154579 : Nat := 4983230072969 + 3 ^ 40 * 1154579 * 2
def baseEnd_1154579 : Nat := 43915109673151365781681

theorem tailTrace_1154579 : CollatzResearch.WordTrace tailWord_1154579 prefixEnd_1154579 43915109673151365781681 := by
  unfold tailWord_1154579
  simp only [CollatzResearch.WordTrace]
  refine ⟨42110955684164944239498791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28073970456109962826332527 42110955684164944239498791)
  ·
    refine ⟨63166433526247416359248187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42110955684164944239498791 63166433526247416359248187)
    ·
      refine ⟨94749650289371124538872281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63166433526247416359248187 94749650289371124538872281)
      ·
        refine ⟨71062237717028343404154211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94749650289371124538872281 71062237717028343404154211)
        ·
          refine ⟨106593356575542515106231317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71062237717028343404154211 106593356575542515106231317)
          ·
            refine ⟨4996563589478555395604593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106593356575542515106231317 4996563589478555395604593)
            ·
              refine ⟨3747422692108916546703445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4996563589478555395604593 3747422692108916546703445)
              ·
                refine ⟨43915109673151365781681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3747422692108916546703445 43915109673151365781681)
                ·
                  rfl

theorem cell22_1154579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 8].length) (baseStart_1154579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154579 prefixEnd_1154579 := by exact prefixLift 1154579
  have htrace : WordTrace (prefixWord ++ tailWord_1154579) baseStart_1154579 baseEnd_1154579 := by
    simpa [prefixWord, tailWord_1154579, baseEnd_1154579] using wordTrace_append hprefix tailTrace_1154579
  have hstable : (prefixWord ++ tailWord_1154579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154579).length < 2 ^ (prefixWord ++ tailWord_1154579).sum := by decide
  have hdescent : baseEnd_1154579 < baseStart_1154579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154581 : List Nat := [1, 3, 2, 1, 3, 2, 1, 3, 2, 4]
def baseStart_1154581 : Nat := 118140960795 + 1154581 * 2 ^ 59
def prefixEnd_1154581 : Nat := 4983230072969 + 3 ^ 40 * 1154581 * 2
def baseEnd_1154581 : Nat := 395236671699234953485123

theorem tailTrace_1154581 : CollatzResearch.WordTrace tailWord_1154581 prefixEnd_1154581 395236671699234953485123 := by
  unfold tailWord_1154581
  simp only [CollatzResearch.WordTrace]
  refine ⟨42111028630157698581071597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28074019086771799054047731 42111028630157698581071597)
  ·
    refine ⟨15791635736309136967901849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42111028630157698581071597 15791635736309136967901849)
    ·
      refine ⟨11843726802231852725926387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15791635736309136967901849 11843726802231852725926387)
      ·
        refine ⟨17765590203347779088889581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11843726802231852725926387 17765590203347779088889581)
        ·
          refine ⟨6662096326255417158333593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17765590203347779088889581 6662096326255417158333593)
          ·
            refine ⟨4996572244691562868750195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6662096326255417158333593 4996572244691562868750195)
            ·
              refine ⟨7494858367037344303125293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4996572244691562868750195 7494858367037344303125293)
              ·
                refine ⟨2810571887639004113671985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7494858367037344303125293 2810571887639004113671985)
                ·
                  refine ⟨2107928915729253085253989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2810571887639004113671985 2107928915729253085253989)
                  ·
                    refine ⟨395236671699234953485123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2107928915729253085253989 395236671699234953485123)
                    ·
                      rfl

theorem cell22_1154581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_1154581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154581 prefixEnd_1154581 := by exact prefixLift 1154581
  have htrace : WordTrace (prefixWord ++ tailWord_1154581) baseStart_1154581 baseEnd_1154581 := by
    simpa [prefixWord, tailWord_1154581, baseEnd_1154581] using wordTrace_append hprefix tailTrace_1154581
  have hstable : (prefixWord ++ tailWord_1154581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154581).length < 2 ^ (prefixWord ++ tailWord_1154581).sum := by decide
  have hdescent : baseEnd_1154581 < baseStart_1154581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154624 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 9]
def baseStart_1154624 : Nat := 118140960795 + 1154624 * 2 ^ 59
def prefixEnd_1154624 : Nat := 4983230072969 + 3 ^ 40 * 1154624 * 2
def baseEnd_1154624 : Nat := 131750463825999058219997

theorem tailTrace_1154624 : CollatzResearch.WordTrace tailWord_1154624 prefixEnd_1154624 131750463825999058219997 := by
  unfold tailWord_1154624
  simp only [CollatzResearch.WordTrace]
  refine ⟨21056298484500958462443463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28075064646001277949924617 21056298484500958462443463)
  ·
    refine ⟨31584447726751437693665195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21056298484500958462443463 31584447726751437693665195)
    ·
      refine ⟨47376671590127156540497793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31584447726751437693665195 47376671590127156540497793)
      ·
        refine ⟨35532503692595367405373345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47376671590127156540497793 35532503692595367405373345)
        ·
          refine ⟨26649377769446525554030009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35532503692595367405373345 26649377769446525554030009)
          ·
            refine ⟨19987033327084894165522507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26649377769446525554030009 19987033327084894165522507)
            ·
              refine ⟨29980549990627341248283761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19987033327084894165522507 29980549990627341248283761)
              ·
                refine ⟨22485412492970505936212821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29980549990627341248283761 22485412492970505936212821)
                ·
                  refine ⟨131750463825999058219997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22485412492970505936212821 131750463825999058219997)
                  ·
                    rfl

theorem cell22_1154624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 9].length) (baseStart_1154624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154624 prefixEnd_1154624 := by exact prefixLift 1154624
  have htrace : WordTrace (prefixWord ++ tailWord_1154624) baseStart_1154624 baseEnd_1154624 := by
    simpa [prefixWord, tailWord_1154624, baseEnd_1154624] using wordTrace_append hprefix tailTrace_1154624
  have hstable : (prefixWord ++ tailWord_1154624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154624).length < 2 ^ (prefixWord ++ tailWord_1154624).sum := by decide
  have hdescent : baseEnd_1154624 < baseStart_1154624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
