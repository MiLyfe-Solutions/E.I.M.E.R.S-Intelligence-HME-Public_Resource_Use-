import V185TrunkScan23Chunk1379

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8173762 : List Nat := [3, 5, 1, 1, 1, 1, 2, 2, 7]
def baseStart_8173762 : Nat := 118140960795 + 8173762 * 2 ^ 59
def prefixEnd_8173762 : Nat := 4983230072969 + 3 ^ 40 * 8173762 * 2
def baseEnd_8173762 : Nat := 466340962383928261364951

theorem tailTrace_8173762 : CollatzResearch.WordTrace tailWord_8173762 prefixEnd_8173762 466340962383928261364951 := by
  unfold tailWord_8173762
  simp only [CollatzResearch.WordTrace]
  refine ⟨74530397953465929064016885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198747727875909144170711693 74530397953465929064016885)
  ·
    refine ⟨6987224808137430849751583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74530397953465929064016885 6987224808137430849751583)
    ·
      refine ⟨10480837212206146274627375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6987224808137430849751583 10480837212206146274627375)
      ·
        refine ⟨15721255818309219411941063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10480837212206146274627375 15721255818309219411941063)
        ·
          refine ⟨23581883727463829117911595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15721255818309219411941063 23581883727463829117911595)
          ·
            refine ⟨35372825591195743676867393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23581883727463829117911595 35372825591195743676867393)
            ·
              refine ⟨26529619193396807757650545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35372825591195743676867393 26529619193396807757650545)
              ·
                refine ⟨19897214395047605818237909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26529619193396807757650545 19897214395047605818237909)
                ·
                  refine ⟨466340962383928261364951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19897214395047605818237909 466340962383928261364951)
                  ·
                    rfl

theorem cell23_8173762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_8173762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173762 prefixEnd_8173762 := by exact prefixLift 8173762
  have htrace : WordTrace (prefixWord ++ tailWord_8173762) baseStart_8173762 baseEnd_8173762 := by
    simpa [prefixWord, tailWord_8173762, baseEnd_8173762] using wordTrace_append hprefix tailTrace_8173762
  have hstable : (prefixWord ++ tailWord_8173762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173762).length < 2 ^ (prefixWord ++ tailWord_8173762).sum := by decide
  have hdescent : baseEnd_8173762 < baseStart_8173762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173771 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 2, 8]
def baseStart_8173771 : Nat := 118140960795 + 8173771 * 2 ^ 59
def prefixEnd_8173771 : Nat := 4983230072969 + 3 ^ 40 * 8173771 * 2
def baseEnd_8173771 : Nat := 1399024427593748272357339

theorem tailTrace_8173771 : CollatzResearch.WordTrace tailWord_8173771 prefixEnd_8173771 1399024427593748272357339 := by
  unfold tailWord_8173771
  simp only [CollatzResearch.WordTrace]
  refine ⟨298121920070831110793145167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198747946713887407195430111 298121920070831110793145167)
  ·
    refine ⟨447182880106246666189717751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298121920070831110793145167 447182880106246666189717751)
    ·
      refine ⟨670774320159369999284576627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447182880106246666189717751 670774320159369999284576627)
      ·
        refine ⟨1006161480239054998926864941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670774320159369999284576627 1006161480239054998926864941)
        ·
          refine ⟨377310555089645624597574353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1006161480239054998926864941 377310555089645624597574353)
          ·
            refine ⟨282982916317234218448180765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377310555089645624597574353 282982916317234218448180765)
            ·
              refine ⟨106118593618962831918067787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282982916317234218448180765 106118593618962831918067787)
              ·
                refine ⟨159177890428444247877101681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106118593618962831918067787 159177890428444247877101681)
                ·
                  refine ⟨119383417821333185907826261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159177890428444247877101681 119383417821333185907826261)
                  ·
                    refine ⟨1399024427593748272357339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119383417821333185907826261 1399024427593748272357339)
                    ·
                      rfl

theorem cell23_8173771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 8].length) (baseStart_8173771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173771 prefixEnd_8173771 := by exact prefixLift 8173771
  have htrace : WordTrace (prefixWord ++ tailWord_8173771) baseStart_8173771 baseEnd_8173771 := by
    simpa [prefixWord, tailWord_8173771, baseEnd_8173771] using wordTrace_append hprefix tailTrace_8173771
  have hstable : (prefixWord ++ tailWord_8173771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173771).length < 2 ^ (prefixWord ++ tailWord_8173771).sum := by decide
  have hdescent : baseEnd_8173771 < baseStart_8173771 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173832 : List Nat := [2, 1, 3, 2, 3, 2, 2, 1, 2, 2, 3]
def baseStart_8173832 : Nat := 118140960795 + 8173832 * 2 ^ 59
def prefixEnd_8173832 : Nat := 4983230072969 + 3 ^ 40 * 8173832 * 2
def baseEnd_8173832 : Nat := 4197104605101169078409237

theorem tailTrace_8173832 : CollatzResearch.WordTrace tailWord_8173832 prefixEnd_8173832 4197104605101169078409237 := by
  unfold tailWord_8173832
  simp only [CollatzResearch.WordTrace]
  refine ⟨149062072461805059105557875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198749429949073412140743833 149062072461805059105557875)
  ·
    refine ⟨223593108692707588658336813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149062072461805059105557875 223593108692707588658336813)
    ·
      refine ⟨83847415759765345746876305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223593108692707588658336813 83847415759765345746876305)
      ·
        refine ⟨62885561819824009310157229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83847415759765345746876305 62885561819824009310157229)
        ·
          refine ⟨23582085682434003491308961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62885561819824009310157229 23582085682434003491308961)
          ·
            refine ⟨17686564261825502618481721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23582085682434003491308961 17686564261825502618481721)
            ·
              refine ⟨13264923196369126963861291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17686564261825502618481721 13264923196369126963861291)
              ·
                refine ⟨19897384794553690445791937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13264923196369126963861291 19897384794553690445791937)
                ·
                  refine ⟨14923038595915267834343953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19897384794553690445791937 14923038595915267834343953)
                  ·
                    refine ⟨11192278946936450875757965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14923038595915267834343953 11192278946936450875757965)
                    ·
                      refine ⟨4197104605101169078409237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11192278946936450875757965 4197104605101169078409237)
                      ·
                        rfl

theorem cell23_8173832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_8173832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173832 prefixEnd_8173832 := by exact prefixLift 8173832
  have htrace : WordTrace (prefixWord ++ tailWord_8173832) baseStart_8173832 baseEnd_8173832 := by
    simpa [prefixWord, tailWord_8173832, baseEnd_8173832] using wordTrace_append hprefix tailTrace_8173832
  have hstable : (prefixWord ++ tailWord_8173832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173832).length < 2 ^ (prefixWord ++ tailWord_8173832).sum := by decide
  have hdescent : baseEnd_8173832 < baseStart_8173832 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173856 : List Nat := [2, 1, 1, 5, 2, 3, 2, 2, 1, 4]
def baseStart_8173856 : Nat := 118140960795 + 8173856 * 2 ^ 59
def prefixEnd_8173856 : Nat := 4983230072969 + 3 ^ 40 * 8173856 * 2
def baseEnd_8173856 : Nat := 1399038976212292328169709

theorem tailTrace_8173856 : CollatzResearch.WordTrace tailWord_8173856 prefixEnd_8173856 1399038976212292328169709 := by
  unfold tailWord_8173856
  simp only [CollatzResearch.WordTrace]
  refine ⟨149062510137761585154994711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198750013517015446873326281 149062510137761585154994711)
  ·
    refine ⟨223593765206642377732492067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149062510137761585154994711 223593765206642377732492067)
    ·
      refine ⟨335390647809963566598738101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223593765206642377732492067 335390647809963566598738101)
      ·
        refine ⟨31442873232184084368631697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 335390647809963566598738101 31442873232184084368631697)
        ·
          refine ⟨23582154924138063276473773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31442873232184084368631697 23582154924138063276473773)
          ·
            refine ⟨8843308096551773728677665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23582154924138063276473773 8843308096551773728677665)
            ·
              refine ⟨6632481072413830296508249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8843308096551773728677665 6632481072413830296508249)
              ·
                refine ⟨4974360804310372722381187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6632481072413830296508249 4974360804310372722381187)
                ·
                  refine ⟨7461541206465559083571781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4974360804310372722381187 7461541206465559083571781)
                  ·
                    refine ⟨1399038976212292328169709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7461541206465559083571781 1399038976212292328169709)
                    ·
                      rfl

theorem cell23_8173856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 1, 4].length) (baseStart_8173856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173856 prefixEnd_8173856 := by exact prefixLift 8173856
  have htrace : WordTrace (prefixWord ++ tailWord_8173856) baseStart_8173856 baseEnd_8173856 := by
    simpa [prefixWord, tailWord_8173856, baseEnd_8173856] using wordTrace_append hprefix tailTrace_8173856
  have hstable : (prefixWord ++ tailWord_8173856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173856).length < 2 ^ (prefixWord ++ tailWord_8173856).sum := by decide
  have hdescent : baseEnd_8173856 < baseStart_8173856 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173888 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 5]
def baseStart_8173888 : Nat := 118140960795 + 8173888 * 2 ^ 59
def prefixEnd_8173888 : Nat := 4983230072969 + 3 ^ 40 * 8173888 * 2
def baseEnd_8173888 : Nat := 4197133360017820859308979

theorem tailTrace_8173888 : CollatzResearch.WordTrace tailWord_8173888 prefixEnd_8173888 4197133360017820859308979 := by
  unfold tailWord_8173888
  simp only [CollatzResearch.WordTrace]
  refine ⟨149063093705703619887577159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198750791607604826516769545 149063093705703619887577159)
  ·
    refine ⟨223594640558555429831365739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149063093705703619887577159 223594640558555429831365739)
    ·
      refine ⟨335391960837833144747048609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223594640558555429831365739 335391960837833144747048609)
      ·
        refine ⟨251543970628374858560286457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335391960837833144747048609 251543970628374858560286457)
        ·
          refine ⟨188657977971281143920214843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251543970628374858560286457 188657977971281143920214843)
          ·
            refine ⟨282986966956921715880322265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188657977971281143920214843 282986966956921715880322265)
            ·
              refine ⟨212240225217691286910241699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282986966956921715880322265 212240225217691286910241699)
              ·
                refine ⟨318360337826536930365362549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212240225217691286910241699 318360337826536930365362549)
                ·
                  refine ⟨29846281671237837221752739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 318360337826536930365362549 29846281671237837221752739)
                  ·
                    refine ⟨44769422506856755832629109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29846281671237837221752739 44769422506856755832629109)
                    ·
                      refine ⟨4197133360017820859308979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44769422506856755832629109 4197133360017820859308979)
                      ·
                        rfl

theorem cell23_8173888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_8173888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173888 prefixEnd_8173888 := by exact prefixLift 8173888
  have htrace : WordTrace (prefixWord ++ tailWord_8173888) baseStart_8173888 baseEnd_8173888 := by
    simpa [prefixWord, tailWord_8173888, baseEnd_8173888] using wordTrace_append hprefix tailTrace_8173888
  have hstable : (prefixWord ++ tailWord_8173888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173888).length < 2 ^ (prefixWord ++ tailWord_8173888).sum := by decide
  have hdescent : baseEnd_8173888 < baseStart_8173888 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173889 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_8173889 : Nat := 118140960795 + 8173889 * 2 ^ 59
def prefixEnd_8173889 : Nat := 4983230072969 + 3 ^ 40 * 8173889 * 2
def baseEnd_8173889 : Nat := 4197133873498475355396475

theorem tailTrace_8173889 : CollatzResearch.WordTrace tailWord_8173889 prefixEnd_8173889 4197133873498475355396475 := by
  unfold tailWord_8173889
  simp only [CollatzResearch.WordTrace]
  refine ⟨298126223884403616945940721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198750815922935744630627147 298126223884403616945940721)
  ·
    refine ⟨223594667913302712709455541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298126223884403616945940721 223594667913302712709455541)
    ·
      refine ⟨20962000116872129316511457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223594667913302712709455541 20962000116872129316511457)
      ·
        refine ⟨15721500087654096987383593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20962000116872129316511457 15721500087654096987383593)
        ·
          refine ⟨11791125065740572740537695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15721500087654096987383593 11791125065740572740537695)
          ·
            refine ⟨17686687598610859110806543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11791125065740572740537695 17686687598610859110806543)
            ·
              refine ⟨26530031397916288666209815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17686687598610859110806543 26530031397916288666209815)
              ·
                refine ⟨39795047096874432999314723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26530031397916288666209815 39795047096874432999314723)
                ·
                  refine ⟨59692570645311649498972085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39795047096874432999314723 59692570645311649498972085)
                  ·
                    refine ⟨5596178497997967140528633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59692570645311649498972085 5596178497997967140528633)
                    ·
                      refine ⟨4197133873498475355396475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5596178497997967140528633 4197133873498475355396475)
                      ·
                        rfl

theorem cell23_8173889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_8173889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173889 prefixEnd_8173889 := by exact prefixLift 8173889
  have htrace : WordTrace (prefixWord ++ tailWord_8173889) baseStart_8173889 baseEnd_8173889 := by
    simpa [prefixWord, tailWord_8173889, baseEnd_8173889] using wordTrace_append hprefix tailTrace_8173889
  have hstable : (prefixWord ++ tailWord_8173889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173889).length < 2 ^ (prefixWord ++ tailWord_8173889).sum := by decide
  have hdescent : baseEnd_8173889 < baseStart_8173889 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173895 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 4, 4]
def baseStart_8173895 : Nat := 118140960795 + 8173895 * 2 ^ 59
def prefixEnd_8173895 : Nat := 4983230072969 + 3 ^ 40 * 8173895 * 2
def baseEnd_8173895 : Nat := 1399045651460800777307149

theorem tailTrace_8173895 : CollatzResearch.WordTrace tailWord_8173895 prefixEnd_8173895 1399045651460800777307149 := by
  unfold tailWord_8173895
  simp only [CollatzResearch.WordTrace]
  refine ⟨298126442722381879970659139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198750961814921253313772759 298126442722381879970659139)
  ·
    refine ⟨447189664083572819955988709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298126442722381879970659139 447189664083572819955988709)
    ·
      refine ⟨83848062015669903741747883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447189664083572819955988709 83848062015669903741747883)
      ·
        refine ⟨125772093023504855612621825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83848062015669903741747883 125772093023504855612621825)
        ·
          refine ⟨94329069767628641709466369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125772093023504855612621825 94329069767628641709466369)
          ·
            refine ⟨70746802325721481282099777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94329069767628641709466369 70746802325721481282099777)
            ·
              refine ⟨53060101744291110961574833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70746802325721481282099777 53060101744291110961574833)
              ·
                refine ⟨39795076308218333221181125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53060101744291110961574833 39795076308218333221181125)
                ·
                  refine ⟨7461576807790937478971461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39795076308218333221181125 7461576807790937478971461)
                  ·
                    refine ⟨1399045651460800777307149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7461576807790937478971461 1399045651460800777307149)
                    ·
                      rfl

theorem cell23_8173895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_8173895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173895 prefixEnd_8173895 := by exact prefixLift 8173895
  have htrace : WordTrace (prefixWord ++ tailWord_8173895) baseStart_8173895 baseEnd_8173895 := by
    simpa [prefixWord, tailWord_8173895, baseEnd_8173895] using wordTrace_append hprefix tailTrace_8173895
  have hstable : (prefixWord ++ tailWord_8173895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173895).length < 2 ^ (prefixWord ++ tailWord_8173895).sum := by decide
  have hdescent : baseEnd_8173895 < baseStart_8173895 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173898 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_8173898 : Nat := 118140960795 + 8173898 * 2 ^ 59
def prefixEnd_8173898 : Nat := 4983230072969 + 3 ^ 40 * 8173898 * 2
def baseEnd_8173898 : Nat := 4197138494824365820183933

theorem tailTrace_8173898 : CollatzResearch.WordTrace tailWord_8173898 prefixEnd_8173898 4197138494824365820183933 := by
  unfold tailWord_8173898
  simp only [CollatzResearch.WordTrace]
  refine ⟨74531638035342752870754587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198751034760914007655345565 74531638035342752870754587)
  ·
    refine ⟨111797457053014129306131881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74531638035342752870754587 111797457053014129306131881)
    ·
      refine ⟨83848092789760596979598911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111797457053014129306131881 83848092789760596979598911)
      ·
        refine ⟨125772139184640895469398367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83848092789760596979598911 125772139184640895469398367)
        ·
          refine ⟨188658208776961343204097551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125772139184640895469398367 188658208776961343204097551)
          ·
            refine ⟨282987313165442014806146327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188658208776961343204097551 282987313165442014806146327)
            ·
              refine ⟨424480969748163022209219491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282987313165442014806146327 424480969748163022209219491)
              ·
                refine ⟨636721454622244533313829237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424480969748163022209219491 636721454622244533313829237)
                ·
                  refine ⟨59692636370835424998171491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 636721454622244533313829237 59692636370835424998171491)
                  ·
                    refine ⟨89538954556253137497257237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59692636370835424998171491 89538954556253137497257237)
                    ·
                      refine ⟨4197138494824365820183933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89538954556253137497257237 4197138494824365820183933)
                      ·
                        rfl

theorem cell23_8173898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_8173898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173898 prefixEnd_8173898 := by exact prefixLift 8173898
  have htrace : WordTrace (prefixWord ++ tailWord_8173898) baseStart_8173898 baseEnd_8173898 := by
    simpa [prefixWord, tailWord_8173898, baseEnd_8173898] using wordTrace_append hprefix tailTrace_8173898
  have hstable : (prefixWord ++ tailWord_8173898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173898).length < 2 ^ (prefixWord ++ tailWord_8173898).sum := by decide
  have hdescent : baseEnd_8173898 < baseStart_8173898 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173922 : List Nat := [3, 3, 2, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_8173922 : Nat := 118140960795 + 8173922 * 2 ^ 59
def prefixEnd_8173922 : Nat := 4983230072969 + 3 ^ 40 * 8173922 * 2
def baseEnd_8173922 : Nat := 4197150818360073726283823

theorem tailTrace_8173922 : CollatzResearch.WordTrace tailWord_8173922 prefixEnd_8173922 4197150818360073726283823 := by
  unfold tailWord_8173922
  simp only [CollatzResearch.WordTrace]
  refine ⟨74531856873321015895473005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198751618328856042387928013 74531856873321015895473005)
  ·
    refine ⟨27949446327495380960802377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74531856873321015895473005 27949446327495380960802377)
    ·
      refine ⟨20962084745621535720601783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27949446327495380960802377 20962084745621535720601783)
      ·
        refine ⟨31443127118432303580902675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20962084745621535720601783 31443127118432303580902675)
        ·
          refine ⟨47164690677648455371354013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31443127118432303580902675 47164690677648455371354013)
          ·
            refine ⟨17686759004118170764257755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47164690677648455371354013 17686759004118170764257755)
            ·
              refine ⟨26530138506177256146386633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17686759004118170764257755 26530138506177256146386633)
              ·
                refine ⟨19897603879632942109789975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26530138506177256146386633 19897603879632942109789975)
                ·
                  refine ⟨29846405819449413164684963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19897603879632942109789975 29846405819449413164684963)
                  ·
                    refine ⟨44769608729174119747027445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29846405819449413164684963 44769608729174119747027445)
                    ·
                      refine ⟨4197150818360073726283823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44769608729174119747027445 4197150818360073726283823)
                      ·
                        rfl

theorem cell23_8173922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_8173922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173922 prefixEnd_8173922 := by exact prefixLift 8173922
  have htrace : WordTrace (prefixWord ++ tailWord_8173922) baseStart_8173922 baseEnd_8173922 := by
    simpa [prefixWord, tailWord_8173922, baseEnd_8173922] using wordTrace_append hprefix tailTrace_8173922
  have hstable : (prefixWord ++ tailWord_8173922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173922).length < 2 ^ (prefixWord ++ tailWord_8173922).sum := by decide
  have hdescent : baseEnd_8173922 < baseStart_8173922 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173935 : List Nat := [1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 3]
def baseStart_8173935 : Nat := 118140960795 + 8173935 * 2 ^ 59
def prefixEnd_8173935 : Nat := 4983230072969 + 3 ^ 40 * 8173935 * 2
def baseEnd_8173935 : Nat := 4197157493608582175421263

theorem tailTrace_8173935 : CollatzResearch.WordTrace tailWord_8173935 prefixEnd_8173935 4197157493608582175421263 := by
  unfold tailWord_8173935
  simp only [CollatzResearch.WordTrace]
  refine ⟨298127901642236966802115259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198751934428157977868076839 298127901642236966802115259)
  ·
    refine ⟨447191852463355450203172889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298127901642236966802115259 447191852463355450203172889)
    ·
      refine ⟨335393889347516587652379667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447191852463355450203172889 335393889347516587652379667)
      ·
        refine ⟨503090834021274881478569501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335393889347516587652379667 503090834021274881478569501)
        ·
          refine ⟨188659062757978080554463563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 503090834021274881478569501 188659062757978080554463563)
          ·
            refine ⟨282988594136967120831695345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188659062757978080554463563 282988594136967120831695345)
            ·
              refine ⟨212241445602725340623771509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282988594136967120831695345 212241445602725340623771509)
              ·
                refine ⟨19897635525255500683478579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 212241445602725340623771509 19897635525255500683478579)
                ·
                  refine ⟨29846453287883251025217869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19897635525255500683478579 29846453287883251025217869)
                  ·
                    refine ⟨11192419982956219134456701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29846453287883251025217869 11192419982956219134456701)
                    ·
                      refine ⟨4197157493608582175421263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11192419982956219134456701 4197157493608582175421263)
                      ·
                        rfl

theorem cell23_8173935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 3].length) (baseStart_8173935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173935 prefixEnd_8173935 := by exact prefixLift 8173935
  have htrace : WordTrace (prefixWord ++ tailWord_8173935) baseStart_8173935 baseEnd_8173935 := by
    simpa [prefixWord, tailWord_8173935, baseEnd_8173935] using wordTrace_append hprefix tailTrace_8173935
  have hstable : (prefixWord ++ tailWord_8173935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173935).length < 2 ^ (prefixWord ++ tailWord_8173935).sum := by decide
  have hdescent : baseEnd_8173935 < baseStart_8173935 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173953 : List Nat := [1, 2, 4, 3, 1, 1, 3, 3, 1, 2, 2]
def baseStart_8173953 : Nat := 118140960795 + 8173953 * 2 ^ 59
def prefixEnd_8173953 : Nat := 4983230072969 + 3 ^ 40 * 8173953 * 2
def baseEnd_8173953 : Nat := 4197166736260363104996181

theorem tailTrace_8173953 : CollatzResearch.WordTrace tailWord_8173953 prefixEnd_8173953 4197166736260363104996181 := by
  unfold tailWord_8173953
  simp only [CollatzResearch.WordTrace]
  refine ⟨298128558156171755876270513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198752372104114503917513675 298128558156171755876270513)
  ·
    refine ⟨223596418617128816907202885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298128558156171755876270513 223596418617128816907202885)
    ·
      refine ⟨41924328490711653170100541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223596418617128816907202885 41924328490711653170100541)
      ·
        refine ⟨15721623184016869938787703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41924328490711653170100541 15721623184016869938787703)
        ·
          refine ⟨23582434776025304908181555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15721623184016869938787703 23582434776025304908181555)
          ·
            refine ⟨35373652164037957362272333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23582434776025304908181555 35373652164037957362272333)
            ·
              refine ⟨13265119561514234010852125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35373652164037957362272333 13265119561514234010852125)
              ·
                refine ⟨4974419835567837754069547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13265119561514234010852125 4974419835567837754069547)
                ·
                  refine ⟨7461629753351756631104321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4974419835567837754069547 7461629753351756631104321)
                  ·
                    refine ⟨5596222315013817473328241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7461629753351756631104321 5596222315013817473328241)
                    ·
                      refine ⟨4197166736260363104996181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5596222315013817473328241 4197166736260363104996181)
                      ·
                        rfl

theorem cell23_8173953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_8173953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173953 prefixEnd_8173953 := by exact prefixLift 8173953
  have htrace : WordTrace (prefixWord ++ tailWord_8173953) baseStart_8173953 baseEnd_8173953 := by
    simpa [prefixWord, tailWord_8173953, baseEnd_8173953] using wordTrace_append hprefix tailTrace_8173953
  have hstable : (prefixWord ++ tailWord_8173953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173953).length < 2 ^ (prefixWord ++ tailWord_8173953).sum := by decide
  have hdescent : baseEnd_8173953 < baseStart_8173953 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173968 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 5, 8]
def baseStart_8173968 : Nat := 118140960795 + 8173968 * 2 ^ 59
def prefixEnd_8173968 : Nat := 4983230072969 + 3 ^ 40 * 8173968 * 2
def baseEnd_8173968 : Nat := 1399058146156726848769537

theorem tailTrace_8173968 : CollatzResearch.WordTrace tailWord_8173968 prefixEnd_8173968 1399058146156726848769537 := by
  unfold tailWord_8173968
  simp only [CollatzResearch.WordTrace]
  refine ⟨149064552625558706719033279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198752736834078275625377705 149064552625558706719033279)
  ·
    refine ⟨223596828938338060078549919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149064552625558706719033279 223596828938338060078549919)
    ·
      refine ⟨335395243407507090117824879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223596828938338060078549919 335395243407507090117824879)
      ·
        refine ⟨503092865111260635176737319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335395243407507090117824879 503092865111260635176737319)
        ·
          refine ⟨754639297666890952765105979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503092865111260635176737319 754639297666890952765105979)
          ·
            refine ⟨1131958946500336429147658969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754639297666890952765105979 1131958946500336429147658969)
            ·
              refine ⟨848969209875252321860744227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1131958946500336429147658969 848969209875252321860744227)
              ·
                refine ⟨1273453814812878482791116341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848969209875252321860744227 1273453814812878482791116341)
                ·
                  refine ⟨119386295138707357761667157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1273453814812878482791116341 119386295138707357761667157)
                  ·
                    refine ⟨1399058146156726848769537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119386295138707357761667157 1399058146156726848769537)
                    ·
                      rfl

theorem cell23_8173968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 8].length) (baseStart_8173968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173968 prefixEnd_8173968 := by exact prefixLift 8173968
  have htrace : WordTrace (prefixWord ++ tailWord_8173968) baseStart_8173968 baseEnd_8173968 := by
    simpa [prefixWord, tailWord_8173968, baseEnd_8173968] using wordTrace_append hprefix tailTrace_8173968
  have hstable : (prefixWord ++ tailWord_8173968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173968).length < 2 ^ (prefixWord ++ tailWord_8173968).sum := by decide
  have hdescent : baseEnd_8173968 < baseStart_8173968 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174009 : List Nat := [1, 2, 1, 4, 3, 2, 1, 2, 1, 4, 2]
def baseStart_8174009 : Nat := 118140960795 + 8174009 * 2 ^ 59
def prefixEnd_8174009 : Nat := 4983230072969 + 3 ^ 40 * 8174009 * 2
def baseEnd_8174009 : Nat := 4197195491177014885895923

theorem tailTrace_8174009 : CollatzResearch.WordTrace tailWord_8174009 prefixEnd_8174009 4197195491177014885895923 := by
  unfold tailWord_8174009
  simp only [CollatzResearch.WordTrace]
  refine ⟨298130600643968877440309081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198753733762645918293539387 298130600643968877440309081)
  ·
    refine ⟨223597950482976658080231811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298130600643968877440309081 223597950482976658080231811)
    ·
      refine ⟨335396925724464987120347717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223597950482976658080231811 335396925724464987120347717)
      ·
        refine ⟨62886923573337185085065197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335396925724464987120347717 62886923573337185085065197)
        ·
          refine ⟨23582596340001444406899449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62886923573337185085065197 23582596340001444406899449)
          ·
            refine ⟨17686947255001083305174587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23582596340001444406899449 17686947255001083305174587)
            ·
              refine ⟨26530420882501624957761881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17686947255001083305174587 26530420882501624957761881)
              ·
                refine ⟨19897815661876218718321411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26530420882501624957761881 19897815661876218718321411)
                ·
                  refine ⟨29846723492814328077482117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19897815661876218718321411 29846723492814328077482117)
                  ·
                    refine ⟨5596260654902686514527897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29846723492814328077482117 5596260654902686514527897)
                    ·
                      refine ⟨4197195491177014885895923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5596260654902686514527897 4197195491177014885895923)
                      ·
                        rfl

theorem cell23_8174009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_8174009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174009 prefixEnd_8174009 := by exact prefixLift 8174009
  have htrace : WordTrace (prefixWord ++ tailWord_8174009) baseStart_8174009 baseEnd_8174009 := by
    simpa [prefixWord, tailWord_8174009, baseEnd_8174009] using wordTrace_append hprefix tailTrace_8174009
  have hstable : (prefixWord ++ tailWord_8174009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174009).length < 2 ^ (prefixWord ++ tailWord_8174009).sum := by decide
  have hdescent : baseEnd_8174009 < baseStart_8174009 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174012 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 2, 1, 5]
def baseStart_8174012 : Nat := 118140960795 + 8174012 * 2 ^ 59
def prefixEnd_8174012 : Nat := 4983230072969 + 3 ^ 40 * 8174012 * 2
def baseEnd_8174012 : Nat := 4197197031618978374158409

theorem tailTrace_8174012 : CollatzResearch.WordTrace tailWord_8174012 prefixEnd_8174012 4197197031618978374158409 := by
  unfold tailWord_8174012
  simp only [CollatzResearch.WordTrace]
  refine ⟨149065355031479004476334145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198753806708638672635112193 149065355031479004476334145)
  ·
    refine ⟨111799016273609253357250609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149065355031479004476334145 111799016273609253357250609)
    ·
      refine ⟨83849262205206940017937957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111799016273609253357250609 83849262205206940017937957)
      ·
        refine ⟨15721736663476301253363367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83849262205206940017937957 15721736663476301253363367)
        ·
          refine ⟨23582604995214451880045051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15721736663476301253363367 23582604995214451880045051)
          ·
            refine ⟨35373907492821677820067577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23582604995214451880045051 35373907492821677820067577)
            ·
              refine ⟨26530430619616258365050683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35373907492821677820067577 26530430619616258365050683)
              ·
                refine ⟨39795645929424387547576025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26530430619616258365050683 39795645929424387547576025)
                ·
                  refine ⟨29846734447068290660682019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39795645929424387547576025 29846734447068290660682019)
                  ·
                    refine ⟨44770101670602435991023029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29846734447068290660682019 44770101670602435991023029)
                    ·
                      refine ⟨4197197031618978374158409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44770101670602435991023029 4197197031618978374158409)
                      ·
                        rfl

theorem cell23_8174012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_8174012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174012 prefixEnd_8174012 := by exact prefixLift 8174012
  have htrace : WordTrace (prefixWord ++ tailWord_8174012) baseStart_8174012 baseEnd_8174012 := by
    simpa [prefixWord, tailWord_8174012, baseEnd_8174012] using wordTrace_append hprefix tailTrace_8174012
  have hstable : (prefixWord ++ tailWord_8174012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174012).length < 2 ^ (prefixWord ++ tailWord_8174012).sum := by decide
  have hdescent : baseEnd_8174012 < baseStart_8174012 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174026 : List Nat := [3, 1, 2, 1, 2, 2, 4, 2, 2, 2, 2]
def baseStart_8174026 : Nat := 118140960795 + 8174026 * 2 ^ 59
def prefixEnd_8174026 : Nat := 4983230072969 + 3 ^ 40 * 8174026 * 2
def baseEnd_8174026 : Nat := 4197204220348141319383345

theorem tailTrace_8174026 : CollatzResearch.WordTrace tailWord_8174026 prefixEnd_8174026 4197204220348141319383345 := by
  unfold tailWord_8174026
  simp only [CollatzResearch.WordTrace]
  refine ⟨74532805171226822335919483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198754147123271526229118621 74532805171226822335919483)
  ·
    refine ⟨111799207756840233503879225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74532805171226822335919483 111799207756840233503879225)
    ·
      refine ⟨83849405817630175127909419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111799207756840233503879225 83849405817630175127909419)
      ·
        refine ⟨125774108726445262691864129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83849405817630175127909419 125774108726445262691864129)
        ·
          refine ⟨94330581544833947018898097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125774108726445262691864129 94330581544833947018898097)
          ·
            refine ⟨70747936158625460264173573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94330581544833947018898097 70747936158625460264173573)
            ·
              refine ⟨13265238029742273799532545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70747936158625460264173573 13265238029742273799532545)
              ·
                refine ⟨9948928522306705349649409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13265238029742273799532545 9948928522306705349649409)
                ·
                  refine ⟨7461696391730029012237057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9948928522306705349649409 7461696391730029012237057)
                  ·
                    refine ⟨5596272293797521759177793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7461696391730029012237057 5596272293797521759177793)
                    ·
                      refine ⟨4197204220348141319383345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5596272293797521759177793 4197204220348141319383345)
                      ·
                        rfl

theorem cell23_8174026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_8174026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174026 prefixEnd_8174026 := by exact prefixLift 8174026
  have htrace : WordTrace (prefixWord ++ tailWord_8174026) baseStart_8174026 baseEnd_8174026 := by
    simpa [prefixWord, tailWord_8174026, baseEnd_8174026] using wordTrace_append hprefix tailTrace_8174026
  have hstable : (prefixWord ++ tailWord_8174026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174026).length < 2 ^ (prefixWord ++ tailWord_8174026).sum := by decide
  have hdescent : baseEnd_8174026 < baseStart_8174026 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174042 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3]
def baseStart_8174042 : Nat := 118140960795 + 8174042 * 2 ^ 59
def prefixEnd_8174042 : Nat := 4983230072969 + 3 ^ 40 * 8174042 * 2
def baseEnd_8174042 : Nat := 4197212436038613256783271

theorem tailTrace_8174042 : CollatzResearch.WordTrace tailWord_8174042 prefixEnd_8174042 4197212436038613256783271 := by
  unfold tailWord_8174042
  simp only [CollatzResearch.WordTrace]
  refine ⟨74532951063212331019065095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198754536168566216050840253 74532951063212331019065095)
  ·
    refine ⟨111799426594818496528597643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74532951063212331019065095 111799426594818496528597643)
    ·
      refine ⟨167699139892227744792896465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111799426594818496528597643 167699139892227744792896465)
      ·
        refine ⟨125774354919170808594672349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167699139892227744792896465 125774354919170808594672349)
        ·
          refine ⟨47165383094689053223002131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125774354919170808594672349 47165383094689053223002131)
          ·
            refine ⟨70748074642033579834503197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47165383094689053223002131 70748074642033579834503197)
            ·
              refine ⟨26530527990762592437938699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70748074642033579834503197 26530527990762592437938699)
              ·
                refine ⟨39795791986143888656908049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26530527990762592437938699 39795791986143888656908049)
                ·
                  refine ⟨29846843989607916492681037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39795791986143888656908049 29846843989607916492681037)
                  ·
                    refine ⟨11192566496102968684755389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29846843989607916492681037 11192566496102968684755389)
                    ·
                      refine ⟨4197212436038613256783271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11192566496102968684755389 4197212436038613256783271)
                      ·
                        rfl

theorem cell23_8174042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_8174042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174042 prefixEnd_8174042 := by exact prefixLift 8174042
  have htrace : WordTrace (prefixWord ++ tailWord_8174042) baseStart_8174042 baseEnd_8174042 := by
    simpa [prefixWord, tailWord_8174042, baseEnd_8174042] using wordTrace_append hprefix tailTrace_8174042
  have hstable : (prefixWord ++ tailWord_8174042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174042).length < 2 ^ (prefixWord ++ tailWord_8174042).sum := by decide
  have hdescent : baseEnd_8174042 < baseStart_8174042 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174062 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 1, 7]
def baseStart_8174062 : Nat := 118140960795 + 8174062 * 2 ^ 59
def prefixEnd_8174062 : Nat := 4983230072969 + 3 ^ 40 * 8174062 * 2
def baseEnd_8174062 : Nat := 1399074235217234392844393

theorem tailTrace_8174062 : CollatzResearch.WordTrace tailWord_8174062 prefixEnd_8174062 1399074235217234392844393 := by
  unfold tailWord_8174062
  simp only [CollatzResearch.WordTrace]
  refine ⟨37266566714097108436498555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198755022475184578327992293 37266566714097108436498555)
  ·
    refine ⟨55899850071145662654747833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37266566714097108436498555 55899850071145662654747833)
    ·
      refine ⟨41924887553359246991060875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55899850071145662654747833 41924887553359246991060875)
      ·
        refine ⟨62887331330038870486591313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41924887553359246991060875 62887331330038870486591313)
        ·
          refine ⟨47165498497529152864943485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62887331330038870486591313 47165498497529152864943485)
          ·
            refine ⟨17687061936573432324353807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47165498497529152864943485 17687061936573432324353807)
            ·
              refine ⟨26530592904860148486530711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17687061936573432324353807 26530592904860148486530711)
              ·
                refine ⟨39795889357290222729796067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26530592904860148486530711 39795889357290222729796067)
                ·
                  refine ⟨59693834035935334094694101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39795889357290222729796067 59693834035935334094694101)
                  ·
                    refine ⟨1399074235217234392844393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59693834035935334094694101 1399074235217234392844393)
                    ·
                      rfl

theorem cell23_8174062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_8174062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174062 prefixEnd_8174062 := by exact prefixLift 8174062
  have htrace : WordTrace (prefixWord ++ tailWord_8174062) baseStart_8174062 baseEnd_8174062 := by
    simpa [prefixWord, tailWord_8174062, baseEnd_8174062] using wordTrace_append hprefix tailTrace_8174062
  have hstable : (prefixWord ++ tailWord_8174062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174062).length < 2 ^ (prefixWord ++ tailWord_8174062).sum := by decide
  have hdescent : baseEnd_8174062 < baseStart_8174062 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174066 : List Nat := [3, 2, 1, 4, 2, 1, 2, 3, 5]
def baseStart_8174066 : Nat := 118140960795 + 8174066 * 2 ^ 59
def prefixEnd_8174066 : Nat := 4983230072969 + 3 ^ 40 * 8174066 * 2
def baseEnd_8174066 : Nat := 466358306619369018098129

theorem tailTrace_8174066 : CollatzResearch.WordTrace tailWord_8174066 prefixEnd_8174066 466358306619369018098129 := by
  unfold tailWord_8174066
  simp only [CollatzResearch.WordTrace]
  refine ⟨74533169901190594043783513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198755119736508250783422701 74533169901190594043783513)
  ·
    refine ⟨55899877425892945532837635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74533169901190594043783513 55899877425892945532837635)
    ·
      refine ⟨83849816138839418299256453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55899877425892945532837635 83849816138839418299256453)
      ·
        refine ⟨15721840526032390931110585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83849816138839418299256453 15721840526032390931110585)
        ·
          refine ⟨11791380394524293198332939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15721840526032390931110585 11791380394524293198332939)
          ·
            refine ⟨17687070591786439797499409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11791380394524293198332939 17687070591786439797499409)
            ·
              refine ⟨13265302943839829848124557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17687070591786439797499409 13265302943839829848124557)
              ·
                refine ⟨4974488603939936193046709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13265302943839829848124557 4974488603939936193046709)
                ·
                  refine ⟨466358306619369018098129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4974488603939936193046709 466358306619369018098129)
                  ·
                    rfl

theorem cell23_8174066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_8174066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174066 prefixEnd_8174066 := by exact prefixLift 8174066
  have htrace : WordTrace (prefixWord ++ tailWord_8174066) baseStart_8174066 baseEnd_8174066 := by
    simpa [prefixWord, tailWord_8174066, baseEnd_8174066] using wordTrace_append hprefix tailTrace_8174066
  have hstable : (prefixWord ++ tailWord_8174066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174066).length < 2 ^ (prefixWord ++ tailWord_8174066).sum := by decide
  have hdescent : baseEnd_8174066 < baseStart_8174066 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174085 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 2, 3, 5]
def baseStart_8174085 : Nat := 118140960795 + 8174085 * 2 ^ 59
def prefixEnd_8174085 : Nat := 4983230072969 + 3 ^ 40 * 8174085 * 2
def baseEnd_8174085 : Nat := 4197234515706756588545573

theorem tailTrace_8174085 : CollatzResearch.WordTrace tailWord_8174085 prefixEnd_8174085 4197234515706756588545573 := by
  unfold tailWord_8174085
  simp only [CollatzResearch.WordTrace]
  refine ⟨298133372591693542420075709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198755581727795694946717139 298133372591693542420075709)
  ·
    refine ⟨111800014721885078407528391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298133372591693542420075709 111800014721885078407528391)
    ·
      refine ⟨167700022082827617611292587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111800014721885078407528391 167700022082827617611292587)
      ·
        refine ⟨251550033124241426416938881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167700022082827617611292587 251550033124241426416938881)
        ·
          refine ⟨188662524843181069812704161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251550033124241426416938881 188662524843181069812704161)
          ·
            refine ⟨141496893632385802359528121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188662524843181069812704161 141496893632385802359528121)
            ·
              refine ⟨106122670224289351769646091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141496893632385802359528121 106122670224289351769646091)
              ·
                refine ⟨159184005336434027654469137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106122670224289351769646091 159184005336434027654469137)
                ·
                  refine ⟨119388004002325520740851853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159184005336434027654469137 119388004002325520740851853)
                  ·
                    refine ⟨44770501500872070277819445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119388004002325520740851853 44770501500872070277819445)
                    ·
                      refine ⟨4197234515706756588545573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44770501500872070277819445 4197234515706756588545573)
                      ·
                        rfl

theorem cell23_8174085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_8174085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174085 prefixEnd_8174085 := by exact prefixLift 8174085
  have htrace : WordTrace (prefixWord ++ tailWord_8174085) baseStart_8174085 baseEnd_8174085 := by
    simpa [prefixWord, tailWord_8174085, baseEnd_8174085] using wordTrace_append hprefix tailTrace_8174085
  have hstable : (prefixWord ++ tailWord_8174085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174085).length < 2 ^ (prefixWord ++ tailWord_8174085).sum := by decide
  have hdescent : baseEnd_8174085 < baseStart_8174085 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174095 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 4]
def baseStart_8174095 : Nat := 118140960795 + 8174095 * 2 ^ 59
def prefixEnd_8174095 : Nat := 4983230072969 + 3 ^ 40 * 8174095 * 2
def baseEnd_8174095 : Nat := 4197239650513301549420527

theorem tailTrace_8174095 : CollatzResearch.WordTrace tailWord_8174095 prefixEnd_8174095 4197239650513301549420527 := by
  unfold tailWord_8174095
  simp only [CollatzResearch.WordTrace]
  refine ⟨298133737321657314127939739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198755824881104876085293159 298133737321657314127939739)
  ·
    refine ⟨447200605982485971191909609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298133737321657314127939739 447200605982485971191909609)
    ·
      refine ⟨335400454486864478393932207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447200605982485971191909609 335400454486864478393932207)
      ·
        refine ⟨503100681730296717590898311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335400454486864478393932207 503100681730296717590898311)
        ·
          refine ⟨754651022595445076386347467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503100681730296717590898311 754651022595445076386347467)
          ·
            refine ⟨1131976533893167614579521201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754651022595445076386347467 1131976533893167614579521201)
            ·
              refine ⟨848982400419875710934640901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1131976533893167614579521201 848982400419875710934640901)
              ·
                refine ⟨159184200078726695800245169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 848982400419875710934640901 159184200078726695800245169)
                ·
                  refine ⟨119388150059045021850183877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159184200078726695800245169 119388150059045021850183877)
                  ·
                    refine ⟨22385278136070941596909477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119388150059045021850183877 22385278136070941596909477)
                    ·
                      refine ⟨4197239650513301549420527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22385278136070941596909477 4197239650513301549420527)
                      ·
                        rfl

theorem cell23_8174095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 4].length) (baseStart_8174095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174095 prefixEnd_8174095 := by exact prefixLift 8174095
  have htrace : WordTrace (prefixWord ++ tailWord_8174095) baseStart_8174095 baseEnd_8174095 := by
    simpa [prefixWord, tailWord_8174095, baseEnd_8174095] using wordTrace_append hprefix tailTrace_8174095
  have hstable : (prefixWord ++ tailWord_8174095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174095).length < 2 ^ (prefixWord ++ tailWord_8174095).sum := by decide
  have hdescent : baseEnd_8174095 < baseStart_8174095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174109 : List Nat := [1, 4, 2, 2, 1, 2, 2, 2, 3, 4]
def baseStart_8174109 : Nat := 118140960795 + 8174109 * 2 ^ 59
def prefixEnd_8174109 : Nat := 4983230072969 + 3 ^ 40 * 8174109 * 2
def baseEnd_8174109 : Nat := 1399082279747488164881821

theorem tailTrace_8174109 : CollatzResearch.WordTrace tailWord_8174109 prefixEnd_8174109 1399082279747488164881821 := by
  unfold tailWord_8174109
  simp only [CollatzResearch.WordTrace]
  refine ⟨298134247943606594518949381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198756165295737729679299587 298134247943606594518949381)
  ·
    refine ⟨55900171489426236472303009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298134247943606594518949381 55900171489426236472303009)
    ·
      refine ⟨41925128617069677354227257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55900171489426236472303009 41925128617069677354227257)
      ·
        refine ⟨31443846462802258015670443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41925128617069677354227257 31443846462802258015670443)
        ·
          refine ⟨47165769694203387023505665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31443846462802258015670443 47165769694203387023505665)
          ·
            refine ⟨35374327270652540267629249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47165769694203387023505665 35374327270652540267629249)
            ·
              refine ⟨26530745452989405200721937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35374327270652540267629249 26530745452989405200721937)
              ·
                refine ⟨19898059089742053900541453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26530745452989405200721937 19898059089742053900541453)
                ·
                  refine ⟨7461772158653270212703045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19898059089742053900541453 7461772158653270212703045)
                  ·
                    refine ⟨1399082279747488164881821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7461772158653270212703045 1399082279747488164881821)
                    ·
                      rfl

theorem cell23_8174109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_8174109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174109 prefixEnd_8174109 := by exact prefixLift 8174109
  have htrace : WordTrace (prefixWord ++ tailWord_8174109) baseStart_8174109 baseEnd_8174109 := by
    simpa [prefixWord, tailWord_8174109, baseEnd_8174109] using wordTrace_append hprefix tailTrace_8174109
  have hstable : (prefixWord ++ tailWord_8174109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174109).length < 2 ^ (prefixWord ++ tailWord_8174109).sum := by decide
  have hdescent : baseEnd_8174109 < baseStart_8174109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174122 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 8]
def baseStart_8174122 : Nat := 118140960795 + 8174122 * 2 ^ 59
def prefixEnd_8174122 : Nat := 4983230072969 + 3 ^ 40 * 8174122 * 2
def baseEnd_8174122 : Nat := 466361501610108104864767

theorem tailTrace_8174122 : CollatzResearch.WordTrace tailWord_8174122 prefixEnd_8174122 466361501610108104864767 := by
  unfold tailWord_8174122
  simp only [CollatzResearch.WordTrace]
  refine ⟨74533680523139874434793155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198756481395039665159448413 74533680523139874434793155)
  ·
    refine ⟨111800520784709811652189733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74533680523139874434793155 111800520784709811652189733)
    ·
      refine ⟨20962597647133089684785575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111800520784709811652189733 20962597647133089684785575)
      ·
        refine ⟨31443896470699634527178363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20962597647133089684785575 31443896470699634527178363)
        ·
          refine ⟨47165844706049451790767545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31443896470699634527178363 47165844706049451790767545)
          ·
            refine ⟨35374383529537088843075659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47165844706049451790767545 35374383529537088843075659)
            ·
              refine ⟨53061575294305633264613489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35374383529537088843075659 53061575294305633264613489)
              ·
                refine ⟨39796181470729224948460117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53061575294305633264613489 39796181470729224948460117)
                ·
                  refine ⟨466361501610108104864767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39796181470729224948460117 466361501610108104864767)
                  ·
                    rfl

theorem cell23_8174122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 8].length) (baseStart_8174122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174122 prefixEnd_8174122 := by exact prefixLift 8174122
  have htrace : WordTrace (prefixWord ++ tailWord_8174122) baseStart_8174122 baseEnd_8174122 := by
    simpa [prefixWord, tailWord_8174122, baseEnd_8174122] using wordTrace_append hprefix tailTrace_8174122
  have hstable : (prefixWord ++ tailWord_8174122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174122).length < 2 ^ (prefixWord ++ tailWord_8174122).sum := by decide
  have hdescent : baseEnd_8174122 < baseStart_8174122 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174186 : List Nat := [3, 1, 3, 2, 1, 1, 5, 1, 1, 5]
def baseStart_8174186 : Nat := 118140960795 + 8174186 * 2 ^ 59
def prefixEnd_8174186 : Nat := 4983230072969 + 3 ^ 40 * 8174186 * 2
def baseEnd_8174186 : Nat := 1399095459084286897794203

theorem tailTrace_8174186 : CollatzResearch.WordTrace tailWord_8174186 prefixEnd_8174186 1399095459084286897794203 := by
  unfold tailWord_8174186
  simp only [CollatzResearch.WordTrace]
  refine ⟨74534264091081909167375603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198758037576218424446334941 74534264091081909167375603)
  ·
    refine ⟨111801396136622863751063405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74534264091081909167375603 111801396136622863751063405)
    ·
      refine ⟨41925523551233573906648777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111801396136622863751063405 41925523551233573906648777)
      ·
        refine ⟨31444142663425180429986583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41925523551233573906648777 31444142663425180429986583)
        ·
          refine ⟨47166213995137770644979875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31444142663425180429986583 47166213995137770644979875)
          ·
            refine ⟨70749320992706655967469813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47166213995137770644979875 70749320992706655967469813)
            ·
              refine ⟨6632748843066248996950295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70749320992706655967469813 6632748843066248996950295)
              ·
                refine ⟨9949123264599373495425443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6632748843066248996950295 9949123264599373495425443)
                ·
                  refine ⟨14923684896899060243138165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9949123264599373495425443 14923684896899060243138165)
                  ·
                    refine ⟨1399095459084286897794203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14923684896899060243138165 1399095459084286897794203)
                    ·
                      rfl

theorem cell23_8174186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_8174186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174186 prefixEnd_8174186 := by exact prefixLift 8174186
  have htrace : WordTrace (prefixWord ++ tailWord_8174186) baseStart_8174186 baseEnd_8174186 := by
    simpa [prefixWord, tailWord_8174186, baseEnd_8174186] using wordTrace_append hprefix tailTrace_8174186
  have hstable : (prefixWord ++ tailWord_8174186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174186).length < 2 ^ (prefixWord ++ tailWord_8174186).sum := by decide
  have hdescent : baseEnd_8174186 < baseStart_8174186 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174199 : List Nat := [1, 1, 3, 1, 1, 3, 3, 4, 2, 4]
def baseStart_8174199 : Nat := 118140960795 + 8174199 * 2 ^ 59
def prefixEnd_8174199 : Nat := 4983230072969 + 3 ^ 40 * 8174199 * 2
def baseEnd_8174199 : Nat := 1399097684167123047506683

theorem tailTrace_8174199 : CollatzResearch.WordTrace tailWord_8174199 prefixEnd_8174199 1399097684167123047506683 := by
  unfold tailWord_8174199
  simp only [CollatzResearch.WordTrace]
  refine ⟨298137530513280539889725651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198758353675520359926483767 298137530513280539889725651)
  ·
    refine ⟨447206295769920809834588477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298137530513280539889725651 447206295769920809834588477)
    ·
      refine ⟨167702360913720303687970679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447206295769920809834588477 167702360913720303687970679)
      ·
        refine ⟨251553541370580455531956019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167702360913720303687970679 251553541370580455531956019)
        ·
          refine ⟨377330312055870683297934029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251553541370580455531956019 377330312055870683297934029)
          ·
            refine ⟨141498867020951506236725261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377330312055870683297934029 141498867020951506236725261)
            ·
              refine ⟨53062075132856814838771973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141498867020951506236725261 53062075132856814838771973)
              ·
                refine ⟨9949139087410652782269745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53062075132856814838771973 9949139087410652782269745)
                ·
                  refine ⟨7461854315557989586702309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9949139087410652782269745 7461854315557989586702309)
                  ·
                    refine ⟨1399097684167123047506683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7461854315557989586702309 1399097684167123047506683)
                    ·
                      rfl

theorem cell23_8174199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 4].length) (baseStart_8174199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174199 prefixEnd_8174199 := by exact prefixLift 8174199
  have htrace : WordTrace (prefixWord ++ tailWord_8174199) baseStart_8174199 baseEnd_8174199 := by
    simpa [prefixWord, tailWord_8174199, baseEnd_8174199] using wordTrace_append hprefix tailTrace_8174199
  have hstable : (prefixWord ++ tailWord_8174199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174199).length < 2 ^ (prefixWord ++ tailWord_8174199).sum := by decide
  have hdescent : baseEnd_8174199 < baseStart_8174199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174209 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_8174209 : Nat := 118140960795 + 8174209 * 2 ^ 59
def prefixEnd_8174209 : Nat := 4983230072969 + 3 ^ 40 * 8174209 * 2
def baseEnd_8174209 : Nat := 4197298187307914103395003

theorem tailTrace_8174209 : CollatzResearch.WordTrace tailWord_8174209 prefixEnd_8174209 4197298187307914103395003 := by
  unfold tailWord_8174209
  simp only [CollatzResearch.WordTrace]
  refine ⟨298137895243244311597589681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198758596828829541065059787 298137895243244311597589681)
  ·
    refine ⟨223603421432433233698192261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298137895243244311597589681 223603421432433233698192261)
    ·
      refine ⟨41925641518581231318411049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223603421432433233698192261 41925641518581231318411049)
      ·
        refine ⟨31444231138935923488808287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41925641518581231318411049 31444231138935923488808287)
        ·
          refine ⟨47166346708403885233212431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31444231138935923488808287 47166346708403885233212431)
          ·
            refine ⟨70749520062605827849818647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47166346708403885233212431 70749520062605827849818647)
            ·
              refine ⟨106124280093908741774727971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70749520062605827849818647 106124280093908741774727971)
              ·
                refine ⟨159186420140863112662091957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106124280093908741774727971 159186420140863112662091957)
                ·
                  refine ⟨14923726888205916812071121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159186420140863112662091957 14923726888205916812071121)
                  ·
                    refine ⟨11192795166154437609053341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14923726888205916812071121 11192795166154437609053341)
                    ·
                      refine ⟨4197298187307914103395003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11192795166154437609053341 4197298187307914103395003)
                      ·
                        rfl

theorem cell23_8174209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_8174209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174209 prefixEnd_8174209 := by exact prefixLift 8174209
  have htrace : WordTrace (prefixWord ++ tailWord_8174209) baseStart_8174209 baseEnd_8174209 := by
    simpa [prefixWord, tailWord_8174209, baseEnd_8174209] using wordTrace_append hprefix tailTrace_8174209
  have hstable : (prefixWord ++ tailWord_8174209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174209).length < 2 ^ (prefixWord ++ tailWord_8174209).sum := by decide
  have hdescent : baseEnd_8174209 < baseStart_8174209 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174226 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_8174226 : Nat := 118140960795 + 8174226 * 2 ^ 59
def prefixEnd_8174226 : Nat := 4983230072969 + 3 ^ 40 * 8174226 * 2
def baseEnd_8174226 : Nat := 4197306916479040536882425

theorem tailTrace_8174226 : CollatzResearch.WordTrace tailWord_8174226 prefixEnd_8174226 4197306916479040536882425 := by
  unfold tailWord_8174226
  simp only [CollatzResearch.WordTrace]
  refine ⟨74534628821045680875239633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198759010189455149000639021 74534628821045680875239633)
  ·
    refine ⟨55900971615784260656429725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74534628821045680875239633 55900971615784260656429725)
    ·
      refine ⟨20962864355919097746161147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55900971615784260656429725 20962864355919097746161147)
      ·
        refine ⟨31444296533878646619241721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20962864355919097746161147 31444296533878646619241721)
        ·
          refine ⟨23583222400408984964431291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31444296533878646619241721 23583222400408984964431291)
          ·
            refine ⟨35374833600613477446646937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23583222400408984964431291 35374833600613477446646937)
            ·
              refine ⟨26531125200460108084985203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35374833600613477446646937 26531125200460108084985203)
              ·
                refine ⟨39796687800690162127477805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26531125200460108084985203 39796687800690162127477805)
                ·
                  refine ⟨14923757925258810797804177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39796687800690162127477805 14923757925258810797804177)
                  ·
                    refine ⟨11192818443944108098353133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14923757925258810797804177 11192818443944108098353133)
                    ·
                      refine ⟨4197306916479040536882425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11192818443944108098353133 4197306916479040536882425)
                      ·
                        rfl

theorem cell23_8174226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_8174226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174226 prefixEnd_8174226 := by exact prefixLift 8174226
  have htrace : WordTrace (prefixWord ++ tailWord_8174226) baseStart_8174226 baseEnd_8174226 := by
    simpa [prefixWord, tailWord_8174226, baseEnd_8174226] using wordTrace_append hprefix tailTrace_8174226
  have hstable : (prefixWord ++ tailWord_8174226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174226).length < 2 ^ (prefixWord ++ tailWord_8174226).sum := by decide
  have hdescent : baseEnd_8174226 < baseStart_8174226 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174240 : List Nat := [2, 1, 1, 4, 5, 1, 2, 1, 1, 1, 4]
def baseStart_8174240 : Nat := 118140960795 + 8174240 * 2 ^ 59
def prefixEnd_8174240 : Nat := 4983230072969 + 3 ^ 40 * 8174240 * 2
def baseEnd_8174240 : Nat := 4197314105208203482107361

theorem tailTrace_8174240 : CollatzResearch.WordTrace tailWord_8174240 prefixEnd_8174240 4197314105208203482107361 := by
  unfold tailWord_8174240
  simp only [CollatzResearch.WordTrace]
  refine ⟨149069512953066001945984087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198759350604088002594645449 149069512953066001945984087)
  ·
    refine ⟨223604269429599002918976131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149069512953066001945984087 223604269429599002918976131)
    ·
      refine ⟨335406404144398504378464197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223604269429599002918976131 335406404144398504378464197)
      ·
        refine ⟨62888700777074719570962037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335406404144398504378464197 62888700777074719570962037)
        ·
          refine ⟨5895815697850754959777691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62888700777074719570962037 5895815697850754959777691)
          ·
            refine ⟨8843723546776132439666537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5895815697850754959777691 8843723546776132439666537)
            ·
              refine ⟨6632792660082099329749903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8843723546776132439666537 6632792660082099329749903)
              ·
                refine ⟨9949188990123148994624855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6632792660082099329749903 9949188990123148994624855)
                ·
                  refine ⟨14923783485184723491937283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9949188990123148994624855 14923783485184723491937283)
                  ·
                    refine ⟨22385675227777085237905925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14923783485184723491937283 22385675227777085237905925)
                    ·
                      refine ⟨4197314105208203482107361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22385675227777085237905925 4197314105208203482107361)
                      ·
                        rfl

theorem cell23_8174240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_8174240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174240 prefixEnd_8174240 := by exact prefixLift 8174240
  have htrace : WordTrace (prefixWord ++ tailWord_8174240) baseStart_8174240 baseEnd_8174240 := by
    simpa [prefixWord, tailWord_8174240, baseEnd_8174240] using wordTrace_append hprefix tailTrace_8174240
  have hstable : (prefixWord ++ tailWord_8174240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174240).length < 2 ^ (prefixWord ++ tailWord_8174240).sum := by decide
  have hdescent : baseEnd_8174240 < baseStart_8174240 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174300 : List Nat := [2, 2, 5, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_8174300 : Nat := 118140960795 + 8174300 * 2 ^ 59
def prefixEnd_8174300 : Nat := 4983230072969 + 3 ^ 40 * 8174300 * 2
def baseEnd_8174300 : Nat := 4197344914047473247357085

theorem tailTrace_8174300 : CollatzResearch.WordTrace tailWord_8174300 prefixEnd_8174300 4197344914047473247357085 := by
  unfold tailWord_8174300
  simp only [CollatzResearch.WordTrace]
  refine ⟨149070607142957317069576177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198760809523943089426101569 149070607142957317069576177)
  ·
    refine ⟨111802955357217987802182133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149070607142957317069576177 111802955357217987802182133)
    ·
      refine ⟨10481527064739186356454575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111802955357217987802182133 10481527064739186356454575)
      ·
        refine ⟨15722290597108779534681863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10481527064739186356454575 15722290597108779534681863)
        ·
          refine ⟨23583435895663169302022795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15722290597108779534681863 23583435895663169302022795)
          ·
            refine ⟨35375153843494753953034193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23583435895663169302022795 35375153843494753953034193)
            ·
              refine ⟨26531365382621065464775645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35375153843494753953034193 26531365382621065464775645)
              ·
                refine ⟨9949262018482899549290867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26531365382621065464775645 9949262018482899549290867)
                ·
                  refine ⟨14923893027724349323936301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9949262018482899549290867 14923893027724349323936301)
                  ·
                    refine ⟨5596459885396630996476113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14923893027724349323936301 5596459885396630996476113)
                    ·
                      refine ⟨4197344914047473247357085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5596459885396630996476113 4197344914047473247357085)
                      ·
                        rfl

theorem cell23_8174300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_8174300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174300 prefixEnd_8174300 := by exact prefixLift 8174300
  have htrace : WordTrace (prefixWord ++ tailWord_8174300) baseStart_8174300 baseEnd_8174300 := by
    simpa [prefixWord, tailWord_8174300, baseEnd_8174300] using wordTrace_append hprefix tailTrace_8174300
  have hstable : (prefixWord ++ tailWord_8174300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174300).length < 2 ^ (prefixWord ++ tailWord_8174300).sum := by decide
  have hdescent : baseEnd_8174300 < baseStart_8174300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174319 : List Nat := [1, 1, 2, 1, 5, 2, 3, 1, 7]
def baseStart_8174319 : Nat := 118140960795 + 8174319 * 2 ^ 59
def prefixEnd_8174319 : Nat := 4983230072969 + 3 ^ 40 * 8174319 * 2
def baseEnd_8174319 : Nat := 466372741131100963668833

theorem tailTrace_8174319 : CollatzResearch.WordTrace tailWord_8174319 prefixEnd_8174319 466372741131100963668833 := by
  unfold tailWord_8174319
  simp only [CollatzResearch.WordTrace]
  refine ⟨298141907272845800384094011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198761271515230533589396007 298141907272845800384094011)
  ·
    refine ⟨447212860909268700576141017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298141907272845800384094011 447212860909268700576141017)
    ·
      refine ⟨335409645681951525432105763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447212860909268700576141017 335409645681951525432105763)
      ·
        refine ⟨503114468522927288148158645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335409645681951525432105763 503114468522927288148158645)
        ·
          refine ⟨47166981424024433263889873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 503114468522927288148158645 47166981424024433263889873)
          ·
            refine ⟨35375236068018324947917405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47166981424024433263889873 35375236068018324947917405)
            ·
              refine ⟨13265713525506871855469027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35375236068018324947917405 13265713525506871855469027)
              ·
                refine ⟨19898570288260307783203541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13265713525506871855469027 19898570288260307783203541)
                ·
                  refine ⟨466372741131100963668833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19898570288260307783203541 466372741131100963668833)
                  ·
                    rfl

theorem cell23_8174319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 7].length) (baseStart_8174319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174319 prefixEnd_8174319 := by exact prefixLift 8174319
  have htrace : WordTrace (prefixWord ++ tailWord_8174319) baseStart_8174319 baseEnd_8174319 := by
    simpa [prefixWord, tailWord_8174319, baseEnd_8174319] using wordTrace_append hprefix tailTrace_8174319
  have hstable : (prefixWord ++ tailWord_8174319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174319).length < 2 ^ (prefixWord ++ tailWord_8174319).sum := by decide
  have hdescent : baseEnd_8174319 < baseStart_8174319 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174329 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 2, 3, 3]
def baseStart_8174329 : Nat := 118140960795 + 8174329 * 2 ^ 59
def prefixEnd_8174329 : Nat := 4983230072969 + 3 ^ 40 * 8174329 * 2
def baseEnd_8174329 : Nat := 4197359804986453633894451

theorem tailTrace_8174329 : CollatzResearch.WordTrace tailWord_8174329 prefixEnd_8174329 4197359804986453633894451 := by
  unfold tailWord_8174329
  simp only [CollatzResearch.WordTrace]
  refine ⟨298142272002809572091958041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198761514668539714727972027 298142272002809572091958041)
  ·
    refine ⟨223606704002107179068968531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298142272002809572091958041 223606704002107179068968531)
    ·
      refine ⟨335410056003160768603452797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223606704002107179068968531 335410056003160768603452797)
      ·
        refine ⟨125778771001185288226294799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335410056003160768603452797 125778771001185288226294799)
        ·
          refine ⟨188668156501777932339442199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125778771001185288226294799 188668156501777932339442199)
          ·
            refine ⟨283002234752666898509163299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188668156501777932339442199 283002234752666898509163299)
            ·
              refine ⟨424503352129000347763744949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283002234752666898509163299 424503352129000347763744949)
              ·
                refine ⟨39797189262093782602851089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 424503352129000347763744949 39797189262093782602851089)
                ·
                  refine ⟨29847891946570336952138317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39797189262093782602851089 29847891946570336952138317)
                  ·
                    refine ⟨11192959479963876357051869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29847891946570336952138317 11192959479963876357051869)
                    ·
                      refine ⟨4197359804986453633894451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11192959479963876357051869 4197359804986453633894451)
                      ·
                        rfl

theorem cell23_8174329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_8174329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174329 prefixEnd_8174329 := by exact prefixLift 8174329
  have htrace : WordTrace (prefixWord ++ tailWord_8174329) baseStart_8174329 baseEnd_8174329 := by
    simpa [prefixWord, tailWord_8174329, baseEnd_8174329] using wordTrace_append hprefix tailTrace_8174329
  have hstable : (prefixWord ++ tailWord_8174329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174329).length < 2 ^ (prefixWord ++ tailWord_8174329).sum := by decide
  have hdescent : baseEnd_8174329 < baseStart_8174329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174330 : List Nat := [3, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2]
def baseStart_8174330 : Nat := 118140960795 + 8174330 * 2 ^ 59
def prefixEnd_8174330 : Nat := 4983230072969 + 3 ^ 40 * 8174330 * 2
def baseEnd_8174330 : Nat := 4197360318467108129981947

theorem tailTrace_8174330 : CollatzResearch.WordTrace tailWord_8174330 prefixEnd_8174330 4197360318467108129981947 := by
  unfold tailWord_8174330
  simp only [CollatzResearch.WordTrace]
  refine ⟨74535577118951487315686111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198761538983870632841829629 74535577118951487315686111)
  ·
    refine ⟨111803365678427230973529167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74535577118951487315686111 111803365678427230973529167)
    ·
      refine ⟨167705048517640846460293751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111803365678427230973529167 167705048517640846460293751)
      ·
        refine ⟨251557572776461269690440627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167705048517640846460293751 251557572776461269690440627)
        ·
          refine ⟨377336359164691904535660941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251557572776461269690440627 377336359164691904535660941)
          ·
            refine ⟨141501134686759464200872853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377336359164691904535660941 141501134686759464200872853)
            ·
              refine ⟨6632865688441849884415915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141501134686759464200872853 6632865688441849884415915)
              ·
                refine ⟨9949298532662774826623873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6632865688441849884415915 9949298532662774826623873)
                ·
                  refine ⟨7461973899497081119967905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9949298532662774826623873 7461973899497081119967905)
                  ·
                    refine ⟨5596480424622810839975929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7461973899497081119967905 5596480424622810839975929)
                    ·
                      refine ⟨4197360318467108129981947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5596480424622810839975929 4197360318467108129981947)
                      ·
                        rfl

theorem cell23_8174330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2].length) (baseStart_8174330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174330 prefixEnd_8174330 := by exact prefixLift 8174330
  have htrace : WordTrace (prefixWord ++ tailWord_8174330) baseStart_8174330 baseEnd_8174330 := by
    simpa [prefixWord, tailWord_8174330, baseEnd_8174330] using wordTrace_append hprefix tailTrace_8174330
  have hstable : (prefixWord ++ tailWord_8174330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174330).length < 2 ^ (prefixWord ++ tailWord_8174330).sum := by decide
  have hdescent : baseEnd_8174330 < baseStart_8174330 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174370 : List Nat := [3, 3, 1, 1, 2, 4, 2, 2, 5]
def baseStart_8174370 : Nat := 118140960795 + 8174370 * 2 ^ 59
def prefixEnd_8174370 : Nat := 4983230072969 + 3 ^ 40 * 8174370 * 2
def baseEnd_8174370 : Nat := 466375650854809774831307

theorem tailTrace_8174370 : CollatzResearch.WordTrace tailWord_8174370 prefixEnd_8174370 466375650854809774831307 := by
  unfold tailWord_8174370
  simp only [CollatzResearch.WordTrace]
  refine ⟨74535941848915259023550141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198762511597107357396133709 74535941848915259023550141)
  ·
    refine ⟨27950978193343222133831303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74535941848915259023550141 27950978193343222133831303)
    ·
      refine ⟨41926467290014833200746955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27950978193343222133831303 41926467290014833200746955)
      ·
        refine ⟨62889700935022249801120433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41926467290014833200746955 62889700935022249801120433)
        ·
          refine ⟨47167275701266687350840325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62889700935022249801120433 47167275701266687350840325)
          ·
            refine ⟨8843864193987503878282561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47167275701266687350840325 8843864193987503878282561)
            ·
              refine ⟨6632898145490627908711921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8843864193987503878282561 6632898145490627908711921)
              ·
                refine ⟨4974673609117970931533941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6632898145490627908711921 4974673609117970931533941)
                ·
                  refine ⟨466375650854809774831307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4974673609117970931533941 466375650854809774831307)
                  ·
                    rfl

theorem cell23_8174370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_8174370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174370 prefixEnd_8174370 := by exact prefixLift 8174370
  have htrace : WordTrace (prefixWord ++ tailWord_8174370) baseStart_8174370 baseEnd_8174370 := by
    simpa [prefixWord, tailWord_8174370, baseEnd_8174370] using wordTrace_append hprefix tailTrace_8174370
  have hstable : (prefixWord ++ tailWord_8174370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174370).length < 2 ^ (prefixWord ++ tailWord_8174370).sum := by decide
  have hdescent : baseEnd_8174370 < baseStart_8174370 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174419 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 3]
def baseStart_8174419 : Nat := 118140960795 + 8174419 * 2 ^ 59
def prefixEnd_8174419 : Nat := 4983230072969 + 3 ^ 40 * 8174419 * 2
def baseEnd_8174419 : Nat := 4197406018245358281769037

theorem tailTrace_8174419 : CollatzResearch.WordTrace tailWord_8174419 prefixEnd_8174419 4197406018245358281769037 := by
  unfold tailWord_8174419
  simp only [CollatzResearch.WordTrace]
  refine ⟨298145554572483517462734311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198763703048322344975156207 298145554572483517462734311)
  ·
    refine ⟨447218331858725276194101467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298145554572483517462734311 447218331858725276194101467)
    ·
      refine ⟨670827497788087914291152201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447218331858725276194101467 670827497788087914291152201)
      ·
        refine ⟨503120623341065935718364151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670827497788087914291152201 503120623341065935718364151)
        ·
          refine ⟨754680935011598903577546227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503120623341065935718364151 754680935011598903577546227)
          ·
            refine ⟨1132021402517398355366319341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754680935011598903577546227 1132021402517398355366319341)
            ·
              refine ⟨424508025944024383262369753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1132021402517398355366319341 424508025944024383262369753)
              ·
                refine ⟨318381019458018287446777315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424508025944024383262369753 318381019458018287446777315)
                ·
                  refine ⟨477571529187027431170165973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318381019458018287446777315 477571529187027431170165973)
                  ·
                    refine ⟨11193082715320955418050765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 477571529187027431170165973 11193082715320955418050765)
                    ·
                      refine ⟨4197406018245358281769037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11193082715320955418050765 4197406018245358281769037)
                      ·
                        rfl

theorem cell23_8174419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 3].length) (baseStart_8174419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174419 prefixEnd_8174419 := by exact prefixLift 8174419
  have htrace : WordTrace (prefixWord ++ tailWord_8174419) baseStart_8174419 baseEnd_8174419 := by
    simpa [prefixWord, tailWord_8174419, baseEnd_8174419] using wordTrace_append hprefix tailTrace_8174419
  have hstable : (prefixWord ++ tailWord_8174419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174419).length < 2 ^ (prefixWord ++ tailWord_8174419).sum := by decide
  have hdescent : baseEnd_8174419 < baseStart_8174419 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174426 : List Nat := [3, 1, 1, 2, 1, 4, 3, 2, 6]
def baseStart_8174426 : Nat := 118140960795 + 8174426 * 2 ^ 59
def prefixEnd_8174426 : Nat := 4983230072969 + 3 ^ 40 * 8174426 * 2
def baseEnd_8174426 : Nat := 466378845845548861597945

theorem tailTrace_8174426 : CollatzResearch.WordTrace tailWord_8174426 prefixEnd_8174426 466378845845548861597945 := by
  unfold tailWord_8174426
  simp only [CollatzResearch.WordTrace]
  refine ⟨74536452470864539414559783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198763873255638771772159421 74536452470864539414559783)
  ·
    refine ⟨111804678706296809121839675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74536452470864539414559783 111804678706296809121839675)
    ·
      refine ⟨167707018059445213682759513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111804678706296809121839675 167707018059445213682759513)
      ·
        refine ⟨125780263544583910262069635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167707018059445213682759513 125780263544583910262069635)
        ·
          refine ⟨188670395316875865393104453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125780263544583910262069635 188670395316875865393104453)
          ·
            refine ⟨35375699121914224761207085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188670395316875865393104453 35375699121914224761207085)
            ·
              refine ⟨13265887170717834285452657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35375699121914224761207085 13265887170717834285452657)
              ·
                refine ⟨9949415378038375714089493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13265887170717834285452657 9949415378038375714089493)
                ·
                  refine ⟨466378845845548861597945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9949415378038375714089493 466378845845548861597945)
                  ·
                    rfl

theorem cell23_8174426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 6].length) (baseStart_8174426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174426 prefixEnd_8174426 := by exact prefixLift 8174426
  have htrace : WordTrace (prefixWord ++ tailWord_8174426) baseStart_8174426 baseEnd_8174426 := by
    simpa [prefixWord, tailWord_8174426, baseEnd_8174426] using wordTrace_append hprefix tailTrace_8174426
  have hstable : (prefixWord ++ tailWord_8174426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174426).length < 2 ^ (prefixWord ++ tailWord_8174426).sum := by decide
  have hdescent : baseEnd_8174426 < baseStart_8174426 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174487 : List Nat := [1, 1, 3, 3, 1, 2, 5, 2, 1, 1, 3]
def baseStart_8174487 : Nat := 118140960795 + 8174487 * 2 ^ 59
def prefixEnd_8174487 : Nat := 4983230072969 + 3 ^ 40 * 8174487 * 2
def baseEnd_8174487 : Nat := 4197440934929864015718725

theorem tailTrace_8174487 : CollatzResearch.WordTrace tailWord_8174487 prefixEnd_8174487 4197440934929864015718725 := by
  unfold tailWord_8174487
  simp only [CollatzResearch.WordTrace]
  refine ⟨298148034736237165076209715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198765356490824776717473143 298148034736237165076209715)
  ·
    refine ⟨447222052104355747614314573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298148034736237165076209715 447222052104355747614314573)
    ·
      refine ⟨167708269539133405355367965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447222052104355747614314573 167708269539133405355367965)
      ·
        refine ⟨62890601077175027008262987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167708269539133405355367965 62890601077175027008262987)
        ·
          refine ⟨94335901615762540512394481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62890601077175027008262987 94335901615762540512394481)
          ·
            refine ⟨70751926211821905384295861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94335901615762540512394481 70751926211821905384295861)
            ·
              refine ⟨6632993082358303629777737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70751926211821905384295861 6632993082358303629777737)
              ·
                refine ⟨4974744811768727722333303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6632993082358303629777737 4974744811768727722333303)
                ·
                  refine ⟨7462117217653091583499955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4974744811768727722333303 7462117217653091583499955)
                  ·
                    refine ⟨11193175826479637375249933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7462117217653091583499955 11193175826479637375249933)
                    ·
                      refine ⟨4197440934929864015718725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11193175826479637375249933 4197440934929864015718725)
                      ·
                        rfl

theorem cell23_8174487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_8174487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174487 prefixEnd_8174487 := by exact prefixLift 8174487
  have htrace : WordTrace (prefixWord ++ tailWord_8174487) baseStart_8174487 baseEnd_8174487 := by
    simpa [prefixWord, tailWord_8174487, baseEnd_8174487] using wordTrace_append hprefix tailTrace_8174487
  have hstable : (prefixWord ++ tailWord_8174487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174487).length < 2 ^ (prefixWord ++ tailWord_8174487).sum := by decide
  have hdescent : baseEnd_8174487 < baseStart_8174487 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174496 : List Nat := [2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 5]
def baseStart_8174496 : Nat := 118140960795 + 8174496 * 2 ^ 59
def prefixEnd_8174496 : Nat := 4983230072969 + 3 ^ 40 * 8174496 * 2
def baseEnd_8174496 : Nat := 4197445556255754480506183

theorem tailTrace_8174496 : CollatzResearch.WordTrace tailWord_8174496 prefixEnd_8174496 4197445556255754480506183 := by
  unfold tailWord_8174496
  simp only [CollatzResearch.WordTrace]
  refine ⟨149074181496602279806643671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198765575328803039742191561 149074181496602279806643671)
  ·
    refine ⟨223611272244903419709965507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149074181496602279806643671 223611272244903419709965507)
    ·
      refine ⟨335416908367355129564948261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223611272244903419709965507 335416908367355129564948261)
      ·
        refine ⟨62890670318879086793427799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335416908367355129564948261 62890670318879086793427799)
        ·
          refine ⟨94336005478318630190141699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62890670318879086793427799 94336005478318630190141699)
          ·
            refine ⟨141504008217477945285212549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94336005478318630190141699 141504008217477945285212549)
            ·
              refine ⟨26532001540777114740977353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141504008217477945285212549 26532001540777114740977353)
              ·
                refine ⟨19899001155582836055733015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26532001540777114740977353 19899001155582836055733015)
                ·
                  refine ⟨29848501733374254083599523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19899001155582836055733015 29848501733374254083599523)
                  ·
                    refine ⟨44772752600061381125399285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29848501733374254083599523 44772752600061381125399285)
                    ·
                      refine ⟨4197445556255754480506183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44772752600061381125399285 4197445556255754480506183)
                      ·
                        rfl

theorem cell23_8174496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_8174496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174496 prefixEnd_8174496 := by exact prefixLift 8174496
  have htrace : WordTrace (prefixWord ++ tailWord_8174496) baseStart_8174496 baseEnd_8174496 := by
    simpa [prefixWord, tailWord_8174496, baseEnd_8174496] using wordTrace_append hprefix tailTrace_8174496
  have hstable : (prefixWord ++ tailWord_8174496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174496).length < 2 ^ (prefixWord ++ tailWord_8174496).sum := by decide
  have hdescent : baseEnd_8174496 < baseStart_8174496 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174499 : List Nat := [1, 1, 1, 4, 1, 2, 3, 10]
def baseStart_8174499 : Nat := 118140960795 + 8174499 * 2 ^ 59
def prefixEnd_8174499 : Nat := 4983230072969 + 3 ^ 40 * 8174499 * 2
def baseEnd_8174499 : Nat := 155461003581396961806247

theorem tailTrace_8174499 : CollatzResearch.WordTrace tailWord_8174499 prefixEnd_8174499 155461003581396961806247 := by
  unfold tailWord_8174499
  simp only [CollatzResearch.WordTrace]
  refine ⟨298148472412193691125646551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198765648274795794083764367 298148472412193691125646551)
  ·
    refine ⟨447222708618290536688469827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298148472412193691125646551 447222708618290536688469827)
    ·
      refine ⟨670834062927435805032704741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447222708618290536688469827 670834062927435805032704741)
      ·
        refine ⟨125781386798894213443632139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 670834062927435805032704741 125781386798894213443632139)
        ·
          refine ⟨188672080198341320165448209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125781386798894213443632139 188672080198341320165448209)
          ·
            refine ⟨141504060148755990124086157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188672080198341320165448209 141504060148755990124086157)
            ·
              refine ⟨53064022555783496296532309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141504060148755990124086157 53064022555783496296532309)
              ·
                refine ⟨155461003581396961806247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53064022555783496296532309 155461003581396961806247)
                ·
                  rfl

theorem cell23_8174499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 10].length) (baseStart_8174499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174499 prefixEnd_8174499 := by exact prefixLift 8174499
  have htrace : WordTrace (prefixWord ++ tailWord_8174499) baseStart_8174499 baseEnd_8174499 := by
    simpa [prefixWord, tailWord_8174499, baseEnd_8174499] using wordTrace_append hprefix tailTrace_8174499
  have hstable : (prefixWord ++ tailWord_8174499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174499).length < 2 ^ (prefixWord ++ tailWord_8174499).sum := by decide
  have hdescent : baseEnd_8174499 < baseStart_8174499 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174550 : List Nat := [5, 2, 1, 1, 2, 3, 1, 8]
def baseStart_8174550 : Nat := 118140960795 + 8174550 * 2 ^ 59
def prefixEnd_8174550 : Nat := 4983230072969 + 3 ^ 40 * 8174550 * 2
def baseEnd_8174550 : Nat := 155461973489299898860405

theorem tailTrace_8174550 : CollatzResearch.WordTrace tailWord_8174550 prefixEnd_8174550 155461973489299898860405 := by
  unfold tailWord_8174550
  simp only [CollatzResearch.WordTrace]
  refine ⟨18634395783438057927234569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198766888356672617890502069 18634395783438057927234569)
  ·
    refine ⟨13975796837578543445425927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18634395783438057927234569 13975796837578543445425927)
    ·
      refine ⟨20963695256367815168138891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13975796837578543445425927 20963695256367815168138891)
      ·
        refine ⟨31445542884551722752208337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20963695256367815168138891 31445542884551722752208337)
        ·
          refine ⟨23584157163413792064156253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31445542884551722752208337 23584157163413792064156253)
          ·
            refine ⟨8844058936280172024058595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23584157163413792064156253 8844058936280172024058595)
            ·
              refine ⟨13266088404420258036087893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8844058936280172024058595 13266088404420258036087893)
              ·
                refine ⟨155461973489299898860405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13266088404420258036087893 155461973489299898860405)
                ·
                  rfl

theorem cell23_8174550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_8174550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174550 prefixEnd_8174550 := by exact prefixLift 8174550
  have htrace : WordTrace (prefixWord ++ tailWord_8174550) baseStart_8174550 baseEnd_8174550 := by
    simpa [prefixWord, tailWord_8174550, baseEnd_8174550] using wordTrace_append hprefix tailTrace_8174550
  have hstable : (prefixWord ++ tailWord_8174550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174550).length < 2 ^ (prefixWord ++ tailWord_8174550).sum := by decide
  have hdescent : baseEnd_8174550 < baseStart_8174550 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174570 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 3, 3, 2]
def baseStart_8174570 : Nat := 118140960795 + 8174570 * 2 ^ 59
def prefixEnd_8174570 : Nat := 4983230072969 + 3 ^ 40 * 8174570 * 2
def baseEnd_8174570 : Nat := 4197483553824187190980843

theorem tailTrace_8174570 : CollatzResearch.WordTrace tailWord_8174570 prefixEnd_8174570 4197483553824187190980843 := by
  unfold tailWord_8174570
  simp only [CollatzResearch.WordTrace]
  refine ⟨74537765498734117562870291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198767374663290980167654109 74537765498734117562870291)
  ·
    refine ⟨111806648248101176344305437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74537765498734117562870291 111806648248101176344305437)
    ·
      refine ⟨41927493093037941129114539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111806648248101176344305437 41927493093037941129114539)
      ·
        refine ⟨62891239639556911693671809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41927493093037941129114539 62891239639556911693671809)
        ·
          refine ⟨47168429729667683770253857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62891239639556911693671809 47168429729667683770253857)
          ·
            refine ⟨35376322297250762827690393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47168429729667683770253857 35376322297250762827690393)
            ·
              refine ⟨26532241722938072120767795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35376322297250762827690393 26532241722938072120767795)
              ·
                refine ⟨39798362584407108181151693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26532241722938072120767795 39798362584407108181151693)
                ·
                  refine ⟨14924385969152665567931885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39798362584407108181151693 14924385969152665567931885)
                  ·
                    refine ⟨5596644738432249587974457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14924385969152665567931885 5596644738432249587974457)
                    ·
                      refine ⟨4197483553824187190980843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5596644738432249587974457 4197483553824187190980843)
                      ·
                        rfl

theorem cell23_8174570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_8174570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174570 prefixEnd_8174570 := by exact prefixLift 8174570
  have htrace : WordTrace (prefixWord ++ tailWord_8174570) baseStart_8174570 baseEnd_8174570 := by
    simpa [prefixWord, tailWord_8174570, baseEnd_8174570] using wordTrace_append hprefix tailTrace_8174570
  have hstable : (prefixWord ++ tailWord_8174570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174570).length < 2 ^ (prefixWord ++ tailWord_8174570).sum := by decide
  have hdescent : baseEnd_8174570 < baseStart_8174570 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174581 : List Nat := [1, 3, 5, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_8174581 : Nat := 118140960795 + 8174581 * 2 ^ 59
def prefixEnd_8174581 : Nat := 4983230072969 + 3 ^ 40 * 8174581 * 2
def baseEnd_8174581 : Nat := 4197489202111386647943293

theorem tailTrace_8174581 : CollatzResearch.WordTrace tailWord_8174581 prefixEnd_8174581 4197489202111386647943293 := by
  unfold tailWord_8174581
  simp only [CollatzResearch.WordTrace]
  refine ⟨298151463197896619130131597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198767642131931079420087731 298151463197896619130131597)
  ·
    refine ⟨111806798699211232173799349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298151463197896619130131597 111806798699211232173799349)
    ·
      refine ⟨10481887378051053016293689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111806798699211232173799349 10481887378051053016293689)
      ·
        refine ⟨7861415533538289762220267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10481887378051053016293689 7861415533538289762220267)
        ·
          refine ⟨11792123300307434643330401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7861415533538289762220267 11792123300307434643330401)
          ·
            refine ⟨8844092475230575982497801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11792123300307434643330401 8844092475230575982497801)
            ·
              refine ⟨6633069356422931986873351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8844092475230575982497801 6633069356422931986873351)
              ·
                refine ⟨9949604034634397980310027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6633069356422931986873351 9949604034634397980310027)
                ·
                  refine ⟨14924406051951596970465041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9949604034634397980310027 14924406051951596970465041)
                  ·
                    refine ⟨11193304538963697727848781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14924406051951596970465041 11193304538963697727848781)
                    ·
                      refine ⟨4197489202111386647943293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11193304538963697727848781 4197489202111386647943293)
                      ·
                        rfl

theorem cell23_8174581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_8174581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174581 prefixEnd_8174581 := by exact prefixLift 8174581
  have htrace : WordTrace (prefixWord ++ tailWord_8174581) baseStart_8174581 baseEnd_8174581 := by
    simpa [prefixWord, tailWord_8174581, baseEnd_8174581] using wordTrace_append hprefix tailTrace_8174581
  have hstable : (prefixWord ++ tailWord_8174581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174581).length < 2 ^ (prefixWord ++ tailWord_8174581).sum := by decide
  have hdescent : baseEnd_8174581 < baseStart_8174581 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174586 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5]
def baseStart_8174586 : Nat := 118140960795 + 8174586 * 2 ^ 59
def prefixEnd_8174586 : Nat := 4983230072969 + 3 ^ 40 * 8174586 * 2
def baseEnd_8174586 : Nat := 4197491769514659128380769

theorem tailTrace_8174586 : CollatzResearch.WordTrace tailWord_8174586 prefixEnd_8174586 4197491769514659128380769 := by
  unfold tailWord_8174586
  simp only [CollatzResearch.WordTrace]
  refine ⟨74537911390719626246015903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198767763708585669989375741 74537911390719626246015903)
  ·
    refine ⟨111806867086079439369023855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74537911390719626246015903 111806867086079439369023855)
    ·
      refine ⟨167710300629119159053535783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111806867086079439369023855 167710300629119159053535783)
      ·
        refine ⟨251565450943678738580303675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167710300629119159053535783 251565450943678738580303675)
        ·
          refine ⟨377348176415518107870455513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251565450943678738580303675 377348176415518107870455513)
          ·
            refine ⟨283011132311638580902841635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377348176415518107870455513 283011132311638580902841635)
            ·
              refine ⟨424516698467457871354262453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283011132311638580902841635 424516698467457871354262453)
              ·
                refine ⟨39798440481324175439462105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 424516698467457871354262453 39798440481324175439462105)
                ·
                  refine ⟨29848830360993131579596579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39798440481324175439462105 29848830360993131579596579)
                  ·
                    refine ⟨44773245541489697369394869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29848830360993131579596579 44773245541489697369394869)
                    ·
                      refine ⟨4197491769514659128380769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44773245541489697369394869 4197491769514659128380769)
                      ·
                        rfl

theorem cell23_8174586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_8174586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174586 prefixEnd_8174586 := by exact prefixLift 8174586
  have htrace : WordTrace (prefixWord ++ tailWord_8174586) baseStart_8174586 baseEnd_8174586 := by
    simpa [prefixWord, tailWord_8174586, baseEnd_8174586] using wordTrace_append hprefix tailTrace_8174586
  have hstable : (prefixWord ++ tailWord_8174586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174586).length < 2 ^ (prefixWord ++ tailWord_8174586).sum := by decide
  have hdescent : baseEnd_8174586 < baseStart_8174586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174594 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_8174594 : Nat := 118140960795 + 8174594 * 2 ^ 59
def prefixEnd_8174594 : Nat := 4983230072969 + 3 ^ 40 * 8174594 * 2
def baseEnd_8174594 : Nat := 4197495877359895097080733

theorem tailTrace_8174594 : CollatzResearch.WordTrace tailWord_8174594 prefixEnd_8174594 4197495877359895097080733 := by
  unfold tailWord_8174594
  simp only [CollatzResearch.WordTrace]
  refine ⟨74537984336712380587588709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198767958231233014900236557 74537984336712380587588709)
  ·
    refine ⟨13975872063133571360172883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74537984336712380587588709 13975872063133571360172883)
    ·
      refine ⟨20963808094700357040259325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13975872063133571360172883 20963808094700357040259325)
      ·
        refine ⟨7861428035512633890097247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20963808094700357040259325 7861428035512633890097247)
        ·
          refine ⟨11792142053268950835145871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7861428035512633890097247 11792142053268950835145871)
          ·
            refine ⟨17688213079903426252718807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11792142053268950835145871 17688213079903426252718807)
            ·
              refine ⟨26532319619855139379078211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17688213079903426252718807 26532319619855139379078211)
              ·
                refine ⟨39798479429782709068617317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26532319619855139379078211 39798479429782709068617317)
                ·
                  refine ⟨7462214893084257950365747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39798479429782709068617317 7462214893084257950365747)
                  ·
                    refine ⟨11193322339626386925548621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7462214893084257950365747 11193322339626386925548621)
                    ·
                      refine ⟨4197495877359895097080733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11193322339626386925548621 4197495877359895097080733)
                      ·
                        rfl

theorem cell23_8174594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_8174594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174594 prefixEnd_8174594 := by exact prefixLift 8174594
  have htrace : WordTrace (prefixWord ++ tailWord_8174594) baseStart_8174594 baseEnd_8174594 := by
    simpa [prefixWord, tailWord_8174594, baseEnd_8174594] using wordTrace_append hprefix tailTrace_8174594
  have hstable : (prefixWord ++ tailWord_8174594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174594).length < 2 ^ (prefixWord ++ tailWord_8174594).sum := by decide
  have hdescent : baseEnd_8174594 < baseStart_8174594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174613 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_8174613 : Nat := 118140960795 + 8174613 * 2 ^ 59
def prefixEnd_8174613 : Nat := 4983230072969 + 3 ^ 40 * 8174613 * 2
def baseEnd_8174613 : Nat := 4197505633492330522743145

theorem tailTrace_8174613 : CollatzResearch.WordTrace tailWord_8174613 prefixEnd_8174613 4197505633492330522743145 := by
  unfold tailWord_8174613
  simp only [CollatzResearch.WordTrace]
  refine ⟨298152630333780688595296493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198768420222520459063530995 298152630333780688595296493)
  ·
    refine ⟨111807236375167758223236185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298152630333780688595296493 111807236375167758223236185)
    ·
      refine ⟨83855427281375818667427139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111807236375167758223236185 83855427281375818667427139)
      ·
        refine ⟨125783140922063728001140709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83855427281375818667427139 125783140922063728001140709)
        ·
          refine ⟨23584338922886949000213883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125783140922063728001140709 23584338922886949000213883)
          ·
            refine ⟨35376508384330423500320825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23584338922886949000213883 35376508384330423500320825)
            ·
              refine ⟨26532381288247817625240619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35376508384330423500320825 26532381288247817625240619)
              ·
                refine ⟨39798571932371726437860929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26532381288247817625240619 39798571932371726437860929)
                ·
                  refine ⟨29848928949278794828395697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39798571932371726437860929 29848928949278794828395697)
                  ·
                    refine ⟨22386696711959096121296773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29848928949278794828395697 22386696711959096121296773)
                    ·
                      refine ⟨4197505633492330522743145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22386696711959096121296773 4197505633492330522743145)
                      ·
                        rfl

theorem cell23_8174613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_8174613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174613 prefixEnd_8174613 := by exact prefixLift 8174613
  have htrace : WordTrace (prefixWord ++ tailWord_8174613) baseStart_8174613 baseEnd_8174613 := by
    simpa [prefixWord, tailWord_8174613, baseEnd_8174613] using wordTrace_append hprefix tailTrace_8174613
  have hstable : (prefixWord ++ tailWord_8174613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174613).length < 2 ^ (prefixWord ++ tailWord_8174613).sum := by decide
  have hdescent : baseEnd_8174613 < baseStart_8174613 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174636 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 1, 7]
def baseStart_8174636 : Nat := 118140960795 + 8174636 * 2 ^ 59
def prefixEnd_8174636 : Nat := 4983230072969 + 3 ^ 40 * 8174636 * 2
def baseEnd_8174636 : Nat := 1399172481182461310918513

theorem tailTrace_8174636 : CollatzResearch.WordTrace tailWord_8174636 prefixEnd_8174636 1399172481182461310918513 := by
  unfold tailWord_8174636
  simp only [CollatzResearch.WordTrace]
  refine ⟨149076734606348681761691881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198768979475131575682255841 149076734606348681761691881)
  ·
    refine ⟨111807550954761511321268911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149076734606348681761691881 111807550954761511321268911)
    ·
      refine ⟨167711326432142266981903367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111807550954761511321268911 167711326432142266981903367)
      ·
        refine ⟨251566989648213400472855051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167711326432142266981903367 251566989648213400472855051)
        ·
          refine ⟨377350484472320100709282577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251566989648213400472855051 377350484472320100709282577)
          ·
            refine ⟨283012863354240075531961933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377350484472320100709282577 283012863354240075531961933)
            ·
              refine ⟨106129823757840028324485725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283012863354240075531961933 106129823757840028324485725)
              ·
                refine ⟨39798683909190010621682147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106129823757840028324485725 39798683909190010621682147)
                ·
                  refine ⟨59698025863785015932523221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39798683909190010621682147 59698025863785015932523221)
                  ·
                    refine ⟨1399172481182461310918513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59698025863785015932523221 1399172481182461310918513)
                    ·
                      rfl

theorem cell23_8174636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_8174636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174636 prefixEnd_8174636 := by exact prefixLift 8174636
  have htrace : WordTrace (prefixWord ++ tailWord_8174636) baseStart_8174636 baseEnd_8174636 := by
    simpa [prefixWord, tailWord_8174636, baseEnd_8174636] using wordTrace_append hprefix tailTrace_8174636
  have hstable : (prefixWord ++ tailWord_8174636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174636).length < 2 ^ (prefixWord ++ tailWord_8174636).sum := by decide
  have hdescent : baseEnd_8174636 < baseStart_8174636 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174643 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 1, 7, 2]
def baseStart_8174643 : Nat := 118140960795 + 8174643 * 2 ^ 59
def prefixEnd_8174643 : Nat := 4983230072969 + 3 ^ 40 * 8174643 * 2
def baseEnd_8174643 : Nat := 4197521037911965405368007

theorem tailTrace_8174643 : CollatzResearch.WordTrace tailWord_8174643 prefixEnd_8174643 4197521037911965405368007 := by
  unfold tailWord_8174643
  simp only [CollatzResearch.WordTrace]
  refine ⟨298153724523672003718888583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198769149682448002479259055 298153724523672003718888583)
  ·
    refine ⟨447230586785508005578332875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298153724523672003718888583 447230586785508005578332875)
    ·
      refine ⟨670845880178262008367499313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447230586785508005578332875 670845880178262008367499313)
      ·
        refine ⟨503134410133696506275624485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670845880178262008367499313 503134410133696506275624485)
        ·
          refine ⟨94337701900068094926679591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 503134410133696506275624485 94337701900068094926679591)
          ·
            refine ⟨141506552850102142390019387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94337701900068094926679591 141506552850102142390019387)
            ·
              refine ⟨212259829275153213585029081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141506552850102142390019387 212259829275153213585029081)
              ·
                refine ⟨159194871956364910188771811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212259829275153213585029081 159194871956364910188771811)
                ·
                  refine ⟨238792307934547365283157717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159194871956364910188771811 238792307934547365283157717)
                  ·
                    refine ⟨5596694717215953873824009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 238792307934547365283157717 5596694717215953873824009)
                    ·
                      refine ⟨4197521037911965405368007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5596694717215953873824009 4197521037911965405368007)
                      ·
                        rfl

theorem cell23_8174643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 7, 2].length) (baseStart_8174643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174643 prefixEnd_8174643 := by exact prefixLift 8174643
  have htrace : WordTrace (prefixWord ++ tailWord_8174643) baseStart_8174643 baseEnd_8174643 := by
    simpa [prefixWord, tailWord_8174643, baseEnd_8174643] using wordTrace_append hprefix tailTrace_8174643
  have hstable : (prefixWord ++ tailWord_8174643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174643).length < 2 ^ (prefixWord ++ tailWord_8174643).sum := by decide
  have hdescent : baseEnd_8174643 < baseStart_8174643 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174653 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 4, 5]
def baseStart_8174653 : Nat := 118140960795 + 8174653 * 2 ^ 59
def prefixEnd_8174653 : Nat := 4983230072969 + 3 ^ 40 * 8174653 * 2
def baseEnd_8174653 : Nat := 1399175390906170122080987

theorem tailTrace_8174653 : CollatzResearch.WordTrace tailWord_8174653 prefixEnd_8174653 1399175390906170122080987 := by
  unfold tailWord_8174653
  simp only [CollatzResearch.WordTrace]
  refine ⟨298154089253635775426752613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198769392835757183617835075 298154089253635775426752613)
  ·
    refine ⟨55903891735056707892516115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298154089253635775426752613 55903891735056707892516115)
    ·
      refine ⟨83855837602585061838774173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55903891735056707892516115 83855837602585061838774173)
      ·
        refine ⟨31445939100969398189540315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83855837602585061838774173 31445939100969398189540315)
        ·
          refine ⟨47168908651454097284310473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31445939100969398189540315 47168908651454097284310473)
          ·
            refine ⟨35376681488590572963232855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47168908651454097284310473 35376681488590572963232855)
            ·
              refine ⟨53065022232885859444849283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35376681488590572963232855 53065022232885859444849283)
              ·
                refine ⟨79597533349328789167273925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53065022232885859444849283 79597533349328789167273925)
                ·
                  refine ⟨14924537502999147968863861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79597533349328789167273925 14924537502999147968863861)
                  ·
                    refine ⟨1399175390906170122080987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14924537502999147968863861 1399175390906170122080987)
                    ·
                      rfl

theorem cell23_8174653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_8174653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174653 prefixEnd_8174653 := by exact prefixLift 8174653
  have htrace : WordTrace (prefixWord ++ tailWord_8174653) baseStart_8174653 baseEnd_8174653 := by
    simpa [prefixWord, tailWord_8174653, baseEnd_8174653] using wordTrace_append hprefix tailTrace_8174653
  have hstable : (prefixWord ++ tailWord_8174653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174653).length < 2 ^ (prefixWord ++ tailWord_8174653).sum := by decide
  have hdescent : baseEnd_8174653 < baseStart_8174653 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174657 : List Nat := [1, 2, 5, 1, 4, 1, 1, 1, 7]
def baseStart_8174657 : Nat := 118140960795 + 8174657 * 2 ^ 59
def prefixEnd_8174657 : Nat := 4983230072969 + 3 ^ 40 * 8174657 * 2
def baseEnd_8174657 : Nat := 466392025182347594510327

theorem tailTrace_8174657 : CollatzResearch.WordTrace tailWord_8174657 prefixEnd_8174657 466392025182347594510327 := by
  unfold tailWord_8174657
  simp only [CollatzResearch.WordTrace]
  refine ⟨298154235145621284109898225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198769490097080856073265483 298154235145621284109898225)
  ·
    refine ⟨223615676359215963082423669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298154235145621284109898225 223615676359215963082423669)
    ·
      refine ⟨20963969658676496538977219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223615676359215963082423669 20963969658676496538977219)
      ·
        refine ⟨31445954488014744808465829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20963969658676496538977219 31445954488014744808465829)
        ·
          refine ⟨5896116466502764651587343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31445954488014744808465829 5896116466502764651587343)
          ·
            refine ⟨8844174699754146977381015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5896116466502764651587343 8844174699754146977381015)
            ·
              refine ⟨13266262049631220466071523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8844174699754146977381015 13266262049631220466071523)
              ·
                refine ⟨19899393074446830699107285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13266262049631220466071523 19899393074446830699107285)
                ·
                  refine ⟨466392025182347594510327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19899393074446830699107285 466392025182347594510327)
                  ·
                    rfl

theorem cell23_8174657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 7].length) (baseStart_8174657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174657 prefixEnd_8174657 := by exact prefixLift 8174657
  have htrace : WordTrace (prefixWord ++ tailWord_8174657) baseStart_8174657 baseEnd_8174657 := by
    simpa [prefixWord, tailWord_8174657, baseEnd_8174657] using wordTrace_append hprefix tailTrace_8174657
  have hstable : (prefixWord ++ tailWord_8174657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174657).length < 2 ^ (prefixWord ++ tailWord_8174657).sum := by decide
  have hdescent : baseEnd_8174657 < baseStart_8174657 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174663 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 5]
def baseStart_8174663 : Nat := 118140960795 + 8174663 * 2 ^ 59
def prefixEnd_8174663 : Nat := 4983230072969 + 3 ^ 40 * 8174663 * 2
def baseEnd_8174663 : Nat := 4197531307525055327117915

theorem tailTrace_8174663 : CollatzResearch.WordTrace tailWord_8174663 prefixEnd_8174663 4197531307525055327117915 := by
  unfold tailWord_8174663
  simp only [CollatzResearch.WordTrace]
  refine ⟨298154453983599547134616643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198769635989066364756411095 298154453983599547134616643)
  ·
    refine ⟨447231680975399320701924965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298154453983599547134616643 447231680975399320701924965)
    ·
      refine ⟨83855940182887372631610931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447231680975399320701924965 83855940182887372631610931)
      ·
        refine ⟨125783910274331058947416397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83855940182887372631610931 125783910274331058947416397)
        ·
          refine ⟨47168966352874147105281149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125783910274331058947416397 47168966352874147105281149)
          ·
            refine ⟨17688362382327805164480431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47168966352874147105281149 17688362382327805164480431)
            ·
              refine ⟨26532543573491707746720647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17688362382327805164480431 26532543573491707746720647)
              ·
                refine ⟨39798815360237561620080971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26532543573491707746720647 39798815360237561620080971)
                ·
                  refine ⟨59698223040356342430121457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39798815360237561620080971 59698223040356342430121457)
                  ·
                    refine ⟨44773667280267256822591093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59698223040356342430121457 44773667280267256822591093)
                    ·
                      refine ⟨4197531307525055327117915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44773667280267256822591093 4197531307525055327117915)
                      ·
                        rfl

theorem cell23_8174663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_8174663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174663 prefixEnd_8174663 := by exact prefixLift 8174663
  have htrace : WordTrace (prefixWord ++ tailWord_8174663) baseStart_8174663 baseEnd_8174663 := by
    simpa [prefixWord, tailWord_8174663, baseEnd_8174663] using wordTrace_append hprefix tailTrace_8174663
  have hstable : (prefixWord ++ tailWord_8174663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174663).length < 2 ^ (prefixWord ++ tailWord_8174663).sum := by decide
  have hdescent : baseEnd_8174663 < baseStart_8174663 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174717 : List Nat := [1, 4, 1, 1, 3, 1, 3, 4, 1, 4]
def baseStart_8174717 : Nat := 118140960795 + 8174717 * 2 ^ 59
def prefixEnd_8174717 : Nat := 4983230072969 + 3 ^ 40 * 8174717 * 2
def baseEnd_8174717 : Nat := 1399186345160132705280889

theorem tailTrace_8174717 : CollatzResearch.WordTrace tailWord_8174717 prefixEnd_8174717 1399186345160132705280889 := by
  unfold tailWord_8174717
  simp only [CollatzResearch.WordTrace]
  refine ⟨298156423525403914357082405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198770949016935942904721603 298156423525403914357082405)
  ·
    refine ⟨55904329411013233941952951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298156423525403914357082405 55904329411013233941952951)
    ·
      refine ⟨83856494116519850912929427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55904329411013233941952951 83856494116519850912929427)
      ·
        refine ⟨125784741174779776369394141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83856494116519850912929427 125784741174779776369394141)
        ·
          refine ⟨47169277940542416138522803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125784741174779776369394141 47169277940542416138522803)
          ·
            refine ⟨70753916910813624207784205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47169277940542416138522803 70753916910813624207784205)
            ·
              refine ⟨26532718841555109077919077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70753916910813624207784205 26532718841555109077919077)
              ·
                refine ⟨4974884782791582952109827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26532718841555109077919077 4974884782791582952109827)
                ·
                  refine ⟨7462327174187374428164741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4974884782791582952109827 7462327174187374428164741)
                  ·
                    refine ⟨1399186345160132705280889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7462327174187374428164741 1399186345160132705280889)
                    ·
                      rfl

theorem cell23_8174717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_8174717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174717 prefixEnd_8174717 := by exact prefixLift 8174717
  have htrace : WordTrace (prefixWord ++ tailWord_8174717) baseStart_8174717 baseEnd_8174717 := by
    simpa [prefixWord, tailWord_8174717, baseEnd_8174717] using wordTrace_append hprefix tailTrace_8174717
  have hstable : (prefixWord ++ tailWord_8174717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174717).length < 2 ^ (prefixWord ++ tailWord_8174717).sum := by decide
  have hdescent : baseEnd_8174717 < baseStart_8174717 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174783 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 5]
def baseStart_8174783 : Nat := 118140960795 + 8174783 * 2 ^ 59
def prefixEnd_8174783 : Nat := 4983230072969 + 3 ^ 40 * 8174783 * 2
def baseEnd_8174783 : Nat := 4197592925203594857617363

theorem tailTrace_8174783 : CollatzResearch.WordTrace tailWord_8174783 prefixEnd_8174783 4197592925203594857617363 := by
  unfold tailWord_8174783
  simp only [CollatzResearch.WordTrace]
  refine ⟨298158830743164807628985003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198772553828776538419323335 298158830743164807628985003)
  ·
    refine ⟨447238246114747211443477505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298158830743164807628985003 447238246114747211443477505)
    ·
      refine ⟨335428684586060408582608129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447238246114747211443477505 335428684586060408582608129)
      ·
        refine ⟨251571513439545306436956097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335428684586060408582608129 251571513439545306436956097)
        ·
          refine ⟨188678635079658979827717073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251571513439545306436956097 188678635079658979827717073)
          ·
            refine ⟨141508976309744234870787805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188678635079658979827717073 141508976309744234870787805)
            ·
              refine ⟨53065866116154088076545427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141508976309744234870787805 53065866116154088076545427)
              ·
                refine ⟨79598799174231132114818141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53065866116154088076545427 79598799174231132114818141)
                ·
                  refine ⟨29849549690336674543056803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79598799174231132114818141 29849549690336674543056803)
                  ·
                    refine ⟨44774324535505011814585205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29849549690336674543056803 44774324535505011814585205)
                    ·
                      refine ⟨4197592925203594857617363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44774324535505011814585205 4197592925203594857617363)
                      ·
                        rfl

theorem cell23_8174783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_8174783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174783 prefixEnd_8174783 := by exact prefixLift 8174783
  have htrace : WordTrace (prefixWord ++ tailWord_8174783) baseStart_8174783 baseEnd_8174783 := by
    simpa [prefixWord, tailWord_8174783, baseEnd_8174783] using wordTrace_append hprefix tailTrace_8174783
  have hstable : (prefixWord ++ tailWord_8174783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174783).length < 2 ^ (prefixWord ++ tailWord_8174783).sum := by decide
  have hdescent : baseEnd_8174783 < baseStart_8174783 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174808 : List Nat := [2, 1, 2, 2, 6, 1, 1, 3, 1, 1, 3]
def baseStart_8174808 : Nat := 118140960795 + 8174808 * 2 ^ 59
def prefixEnd_8174808 : Nat := 4983230072969 + 3 ^ 40 * 8174808 * 2
def baseEnd_8174808 : Nat := 4197605762219957259804749

theorem tailTrace_8174808 : CollatzResearch.WordTrace tailWord_8174808 prefixEnd_8174808 4197605762219957259804749 := by
  unfold tailWord_8174808
  simp only [CollatzResearch.WordTrace]
  refine ⟨149079871284037118449322539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198773161712049491265763385 149079871284037118449322539)
  ·
    refine ⟨223619806926055677673983809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149079871284037118449322539 223619806926055677673983809)
    ·
      refine ⟨167714855194541758255487857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223619806926055677673983809 167714855194541758255487857)
      ·
        refine ⟨125786141395906318691615893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167714855194541758255487857 125786141395906318691615893)
        ·
          refine ⟨5896225377933108688669495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 125786141395906318691615893 5896225377933108688669495)
          ·
            refine ⟨8844338066899663033004243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5896225377933108688669495 8844338066899663033004243)
            ·
              refine ⟨13266507100349494549506365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8844338066899663033004243 13266507100349494549506365)
              ·
                refine ⟨4974940162631060456064887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13266507100349494549506365 4974940162631060456064887)
                ·
                  refine ⟨7462410243946590684097331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4974940162631060456064887 7462410243946590684097331)
                  ·
                    refine ⟨11193615365919886026145997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7462410243946590684097331 11193615365919886026145997)
                    ·
                      refine ⟨4197605762219957259804749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11193615365919886026145997 4197605762219957259804749)
                      ·
                        rfl

theorem cell23_8174808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 1, 1, 3].length) (baseStart_8174808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174808 prefixEnd_8174808 := by exact prefixLift 8174808
  have htrace : WordTrace (prefixWord ++ tailWord_8174808) baseStart_8174808 baseEnd_8174808 := by
    simpa [prefixWord, tailWord_8174808, baseEnd_8174808] using wordTrace_append hprefix tailTrace_8174808
  have hstable : (prefixWord ++ tailWord_8174808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174808).length < 2 ^ (prefixWord ++ tailWord_8174808).sum := by decide
  have hdescent : baseEnd_8174808 < baseStart_8174808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174817 : List Nat := [1, 2, 3, 1, 3, 2, 2, 3, 1, 2, 3]
def baseStart_8174817 : Nat := 118140960795 + 8174817 * 2 ^ 59
def prefixEnd_8174817 : Nat := 4983230072969 + 3 ^ 40 * 8174817 * 2
def baseEnd_8174817 : Nat := 4197610383545847724592207

theorem tailTrace_8174817 : CollatzResearch.WordTrace tailWord_8174817 prefixEnd_8174817 4197610383545847724592207 := by
  unfold tailWord_8174817
  simp only [CollatzResearch.WordTrace]
  refine ⟨298160070825041631435722705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198773380550027754290481803 298160070825041631435722705)
  ·
    refine ⟨223620053118781223576792029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298160070825041631435722705 223620053118781223576792029)
    ·
      refine ⟨83857519919542958841297011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223620053118781223576792029 83857519919542958841297011)
      ·
        refine ⟨125786279879314438261945517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83857519919542958841297011 125786279879314438261945517)
        ·
          refine ⟨47169854954742914348229569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125786279879314438261945517 47169854954742914348229569)
          ·
            refine ⟨35377391216057185761172177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47169854954742914348229569 35377391216057185761172177)
            ·
              refine ⟨26533043412042889320879133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35377391216057185761172177 26533043412042889320879133)
              ·
                refine ⟨9949891279516083495329675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26533043412042889320879133 9949891279516083495329675)
                ·
                  refine ⟨14924836919274125242994513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9949891279516083495329675 14924836919274125242994513)
                  ·
                    refine ⟨11193627689455593932245885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14924836919274125242994513 11193627689455593932245885)
                    ·
                      refine ⟨4197610383545847724592207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11193627689455593932245885 4197610383545847724592207)
                      ·
                        rfl

theorem cell23_8174817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_8174817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174817 prefixEnd_8174817 := by exact prefixLift 8174817
  have htrace : WordTrace (prefixWord ++ tailWord_8174817) baseStart_8174817 baseEnd_8174817 := by
    simpa [prefixWord, tailWord_8174817, baseEnd_8174817] using wordTrace_append hprefix tailTrace_8174817
  have hstable : (prefixWord ++ tailWord_8174817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174817).length < 2 ^ (prefixWord ++ tailWord_8174817).sum := by decide
  have hdescent : baseEnd_8174817 < baseStart_8174817 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174831 : List Nat := [1, 1, 2, 1, 7, 2, 1, 1, 3, 2, 2]
def baseStart_8174831 : Nat := 118140960795 + 8174831 * 2 ^ 59
def prefixEnd_8174831 : Nat := 4983230072969 + 3 ^ 40 * 8174831 * 2
def baseEnd_8174831 : Nat := 4197617572275010669817143

theorem tailTrace_8174831 : CollatzResearch.WordTrace tailWord_8174831 prefixEnd_8174831 4197617572275010669817143 := by
  unfold tailWord_8174831
  simp only [CollatzResearch.WordTrace]
  refine ⟨298160581446990911826732347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198773720964660607884488231 298160581446990911826732347)
  ·
    refine ⟨447240872170486367740098521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298160581446990911826732347 447240872170486367740098521)
    ·
      refine ⟨335430654127864775805073891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447240872170486367740098521 335430654127864775805073891)
      ·
        refine ⟨503145981191797163707610837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335430654127864775805073891 503145981191797163707610837)
        ·
          refine ⟨11792483934182746024397129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 503145981191797163707610837 11792483934182746024397129)
          ·
            refine ⟨8844362950637059518297847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11792483934182746024397129 8844362950637059518297847)
            ·
              refine ⟨13266544425955589277446771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8844362950637059518297847 13266544425955589277446771)
              ·
                refine ⟨19899816638933383916170157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13266544425955589277446771 19899816638933383916170157)
                ·
                  refine ⟨7462431239600018968563809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19899816638933383916170157 7462431239600018968563809)
                  ·
                    refine ⟨5596823429700014226422857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7462431239600018968563809 5596823429700014226422857)
                    ·
                      refine ⟨4197617572275010669817143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5596823429700014226422857 4197617572275010669817143)
                      ·
                        rfl

theorem cell23_8174831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 2, 2].length) (baseStart_8174831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174831 prefixEnd_8174831 := by exact prefixLift 8174831
  have htrace : WordTrace (prefixWord ++ tailWord_8174831) baseStart_8174831 baseEnd_8174831 := by
    simpa [prefixWord, tailWord_8174831, baseEnd_8174831] using wordTrace_append hprefix tailTrace_8174831
  have hstable : (prefixWord ++ tailWord_8174831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174831).length < 2 ^ (prefixWord ++ tailWord_8174831).sum := by decide
  have hdescent : baseEnd_8174831 < baseStart_8174831 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174833 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 2, 7]
def baseStart_8174833 : Nat := 118140960795 + 8174833 * 2 ^ 59
def prefixEnd_8174833 : Nat := 4983230072969 + 3 ^ 40 * 8174833 * 2
def baseEnd_8174833 : Nat := 1399206199745439887330711

theorem tailTrace_8174833 : CollatzResearch.WordTrace tailWord_8174833 prefixEnd_8174833 1399206199745439887330711 := by
  unfold tailWord_8174833
  simp only [CollatzResearch.WordTrace]
  refine ⟨298160654392983666168305153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198773769595322444112203435 298160654392983666168305153)
  ·
    refine ⟨223620490794737749626228865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298160654392983666168305153 223620490794737749626228865)
    ·
      refine ⟨167715368096053312219671649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223620490794737749626228865 167715368096053312219671649)
      ·
        refine ⟨125786526072039984164753737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167715368096053312219671649 125786526072039984164753737)
        ·
          refine ⟨94339894554029988123565303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125786526072039984164753737 94339894554029988123565303)
          ·
            refine ⟨141509841831044982185347955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94339894554029988123565303 141509841831044982185347955)
            ·
              refine ⟨212264762746567473278021933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141509841831044982185347955 212264762746567473278021933)
              ·
                refine ⟨79599286029962802479258225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212264762746567473278021933 79599286029962802479258225)
                ·
                  refine ⟨59699464522472101859443669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79599286029962802479258225 59699464522472101859443669)
                  ·
                    refine ⟨1399206199745439887330711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59699464522472101859443669 1399206199745439887330711)
                    ·
                      rfl

theorem cell23_8174833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_8174833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174833 prefixEnd_8174833 := by exact prefixLift 8174833
  have htrace : WordTrace (prefixWord ++ tailWord_8174833) baseStart_8174833 baseEnd_8174833 := by
    simpa [prefixWord, tailWord_8174833, baseEnd_8174833] using wordTrace_append hprefix tailTrace_8174833
  have hstable : (prefixWord ++ tailWord_8174833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174833).length < 2 ^ (prefixWord ++ tailWord_8174833).sum := by decide
  have hdescent : baseEnd_8174833 < baseStart_8174833 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174840 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 1, 9, 2]
def baseStart_8174840 : Nat := 118140960795 + 8174840 * 2 ^ 59
def prefixEnd_8174840 : Nat := 4983230072969 + 3 ^ 40 * 8174840 * 2
def baseEnd_8174840 : Nat := 4197622193600901134604601

theorem tailTrace_8174840 : CollatzResearch.WordTrace tailWord_8174840 prefixEnd_8174840 4197622193600901134604601 := by
  unfold tailWord_8174840
  simp only [CollatzResearch.WordTrace]
  refine ⟨149080454851979153181904987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198773939802638870909206649 149080454851979153181904987)
  ·
    refine ⟨223620682277968729772857481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149080454851979153181904987 223620682277968729772857481)
    ·
      refine ⟨167715511708476547329643111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223620682277968729772857481 167715511708476547329643111)
      ·
        refine ⟨251573267562714820994464667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167715511708476547329643111 251573267562714820994464667)
        ·
          refine ⟨377359901344072231491697001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251573267562714820994464667 377359901344072231491697001)
          ·
            refine ⟨283019926008054173618772751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377359901344072231491697001 283019926008054173618772751)
            ·
              refine ⟨424529889012081260428159127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283019926008054173618772751 424529889012081260428159127)
              ·
                refine ⟨636794833518121890642238691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424529889012081260428159127 636794833518121890642238691)
                ·
                  refine ⟨955192250277182835963358037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636794833518121890642238691 955192250277182835963358037)
                  ·
                    refine ⟨5596829591467868179472801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 955192250277182835963358037 5596829591467868179472801)
                    ·
                      refine ⟨4197622193600901134604601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5596829591467868179472801 4197622193600901134604601)
                      ·
                        rfl

theorem cell23_8174840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 9, 2].length) (baseStart_8174840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174840 prefixEnd_8174840 := by exact prefixLift 8174840
  have htrace : WordTrace (prefixWord ++ tailWord_8174840) baseStart_8174840 baseEnd_8174840 := by
    simpa [prefixWord, tailWord_8174840, baseEnd_8174840] using wordTrace_append hprefix tailTrace_8174840
  have hstable : (prefixWord ++ tailWord_8174840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174840).length < 2 ^ (prefixWord ++ tailWord_8174840).sum := by decide
  have hdescent : baseEnd_8174840 < baseStart_8174840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174857 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 3, 3, 2]
def baseStart_8174857 : Nat := 118140960795 + 8174857 * 2 ^ 59
def prefixEnd_8174857 : Nat := 4983230072969 + 3 ^ 40 * 8174857 * 2
def baseEnd_8174857 : Nat := 4197630922772027568092023

theorem tailTrace_8174857 : CollatzResearch.WordTrace tailWord_8174857 prefixEnd_8174857 4197630922772027568092023 := by
  unfold tailWord_8174857
  simp only [CollatzResearch.WordTrace]
  refine ⟨298161529744896718267178825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198774353163264478844785883 298161529744896718267178825)
  ·
    refine ⟨223621147308672538700384119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298161529744896718267178825 223621147308672538700384119)
    ·
      refine ⟨335431720963008808050576179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223621147308672538700384119 335431720963008808050576179)
      ·
        refine ⟨503147581444513212075864269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335431720963008808050576179 503147581444513212075864269)
        ·
          refine ⟨188680343041692454528449101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 503147581444513212075864269 188680343041692454528449101)
          ·
            refine ⟨70755128640634670448168413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188680343041692454528449101 70755128640634670448168413)
            ·
              refine ⟨26533173240238001418063155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70755128640634670448168413 26533173240238001418063155)
              ·
                refine ⟨39799759860357002127094733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26533173240238001418063155 39799759860357002127094733)
                ·
                  refine ⟨14924909947633875797660525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39799759860357002127094733 14924909947633875797660525)
                  ·
                    refine ⟨5596841230362703424122697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14924909947633875797660525 5596841230362703424122697)
                    ·
                      refine ⟨4197630922772027568092023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5596841230362703424122697 4197630922772027568092023)
                      ·
                        rfl

theorem cell23_8174857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 3, 2].length) (baseStart_8174857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174857 prefixEnd_8174857 := by exact prefixLift 8174857
  have htrace : WordTrace (prefixWord ++ tailWord_8174857) baseStart_8174857 baseEnd_8174857 := by
    simpa [prefixWord, tailWord_8174857, baseEnd_8174857] using wordTrace_append hprefix tailTrace_8174857
  have hstable : (prefixWord ++ tailWord_8174857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174857).length < 2 ^ (prefixWord ++ tailWord_8174857).sum := by decide
  have hdescent : baseEnd_8174857 < baseStart_8174857 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174863 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 6, 6]
def baseStart_8174863 : Nat := 118140960795 + 8174863 * 2 ^ 59
def prefixEnd_8174863 : Nat := 4983230072969 + 3 ^ 40 * 8174863 * 2
def baseEnd_8174863 : Nat := 1399211334551984848205665

theorem tailTrace_8174863 : CollatzResearch.WordTrace tailWord_8174863 prefixEnd_8174863 1399211334551984848205665 := by
  unfold tailWord_8174863
  simp only [CollatzResearch.WordTrace]
  refine ⟨298161748582874981291897243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198774499055249987527931495 298161748582874981291897243)
  ·
    refine ⟨447242622874312471937845865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298161748582874981291897243 447242622874312471937845865)
    ·
      refine ⟨335431967155734353953384399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447242622874312471937845865 335431967155734353953384399)
      ·
        refine ⟨503147950733601530930076599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335431967155734353953384399 503147950733601530930076599)
        ·
          refine ⟨754721926100402296395114899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503147950733601530930076599 754721926100402296395114899)
          ·
            refine ⟨1132082889150603444592672349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754721926100402296395114899 1132082889150603444592672349)
            ·
              refine ⟨424531083431476291722252131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1132082889150603444592672349 424531083431476291722252131)
              ·
                refine ⟨636796625147214437583378197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424531083431476291722252131 636796625147214437583378197)
                ·
                  refine ⟨29849841803775676761720853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 636796625147214437583378197 29849841803775676761720853)
                  ·
                    refine ⟨1399211334551984848205665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29849841803775676761720853 1399211334551984848205665)
                    ·
                      rfl

theorem cell23_8174863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 6].length) (baseStart_8174863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174863 prefixEnd_8174863 := by exact prefixLift 8174863
  have htrace : WordTrace (prefixWord ++ tailWord_8174863) baseStart_8174863 baseEnd_8174863 := by
    simpa [prefixWord, tailWord_8174863, baseEnd_8174863] using wordTrace_append hprefix tailTrace_8174863
  have hstable : (prefixWord ++ tailWord_8174863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174863).length < 2 ^ (prefixWord ++ tailWord_8174863).sum := by decide
  have hdescent : baseEnd_8174863 < baseStart_8174863 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174882 : List Nat := [3, 3, 1, 1, 5, 1, 2, 2, 1, 2, 2]
def baseStart_8174882 : Nat := 118140960795 + 8174882 * 2 ^ 59
def prefixEnd_8174882 : Nat := 4983230072969 + 3 ^ 40 * 8174882 * 2
def baseEnd_8174882 : Nat := 4197643759788389970279409

theorem tailTrace_8174882 : CollatzResearch.WordTrace tailWord_8174882 prefixEnd_8174882 4197643759788389970279409 := by
  unfold tailWord_8174882
  simp only [CollatzResearch.WordTrace]
  refine ⟨74540610392451536884209725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198774961046537431691225933 74540610392451536884209725)
  ·
    refine ⟨27952728897169326331578647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74540610392451536884209725 27952728897169326331578647)
    ·
      refine ⟨41929093345753989497367971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27952728897169326331578647 41929093345753989497367971)
      ·
        refine ⟨62893640018630984246051957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41929093345753989497367971 62893640018630984246051957)
        ·
          refine ⟨5896278751746654773067371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62893640018630984246051957 5896278751746654773067371)
          ·
            refine ⟨8844418127619982159601057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5896278751746654773067371 8844418127619982159601057)
            ·
              refine ⟨6633313595714986619700793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8844418127619982159601057 6633313595714986619700793)
              ·
                refine ⟨4974985196786239964775595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6633313595714986619700793 4974985196786239964775595)
                ·
                  refine ⟨7462477795179359947163393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4974985196786239964775595 7462477795179359947163393)
                  ·
                    refine ⟨5596858346384519960372545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7462477795179359947163393 5596858346384519960372545)
                    ·
                      refine ⟨4197643759788389970279409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5596858346384519960372545 4197643759788389970279409)
                      ·
                        rfl

theorem cell23_8174882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_8174882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174882 prefixEnd_8174882 := by exact prefixLift 8174882
  have htrace : WordTrace (prefixWord ++ tailWord_8174882) baseStart_8174882 baseEnd_8174882 := by
    simpa [prefixWord, tailWord_8174882, baseEnd_8174882] using wordTrace_append hprefix tailTrace_8174882
  have hstable : (prefixWord ++ tailWord_8174882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174882).length < 2 ^ (prefixWord ++ tailWord_8174882).sum := by decide
  have hdescent : baseEnd_8174882 < baseStart_8174882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174920 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 3, 5, 3]
def baseStart_8174920 : Nat := 118140960795 + 8174920 * 2 ^ 59
def prefixEnd_8174920 : Nat := 4983230072969 + 3 ^ 40 * 8174920 * 2
def baseEnd_8174920 : Nat := 4197663272053260821604233

theorem tailTrace_8174920 : CollatzResearch.WordTrace tailWord_8174920 prefixEnd_8174920 4197663272053260821604233 := by
  unfold tailWord_8174920
  simp only [CollatzResearch.WordTrace]
  refine ⟨149081913771834240013361107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198775885029112320017814809 149081913771834240013361107)
  ·
    refine ⟨223622870657751360020041661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149081913771834240013361107 223622870657751360020041661)
    ·
      refine ⟨83858576496656760007515623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223622870657751360020041661 83858576496656760007515623)
      ·
        refine ⟨125787864744985140011273435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83858576496656760007515623 125787864744985140011273435)
        ·
          refine ⟨188681797117477710016910153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125787864744985140011273435 188681797117477710016910153)
          ·
            refine ⟨141511347838108282512682615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188681797117477710016910153 141511347838108282512682615)
            ·
              refine ⟨212267021757162423769023923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141511347838108282512682615 212267021757162423769023923)
              ·
                refine ⟨318400532635743635653535885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212267021757162423769023923 318400532635743635653535885)
                ·
                  refine ⟨119400199738403863370075957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 318400532635743635653535885 119400199738403863370075957)
                  ·
                    refine ⟨11193768725475362190944621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119400199738403863370075957 11193768725475362190944621)
                    ·
                      refine ⟨4197663272053260821604233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11193768725475362190944621 4197663272053260821604233)
                      ·
                        rfl

theorem cell23_8174920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_8174920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174920 prefixEnd_8174920 := by exact prefixLift 8174920
  have htrace : WordTrace (prefixWord ++ tailWord_8174920) baseStart_8174920 baseEnd_8174920 := by
    simpa [prefixWord, tailWord_8174920, baseEnd_8174920] using wordTrace_append hprefix tailTrace_8174920
  have hstable : (prefixWord ++ tailWord_8174920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174920).length < 2 ^ (prefixWord ++ tailWord_8174920).sum := by decide
  have hdescent : baseEnd_8174920 < baseStart_8174920 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174960 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 4]
def baseStart_8174960 : Nat := 118140960795 + 8174960 * 2 ^ 59
def prefixEnd_8174960 : Nat := 4983230072969 + 3 ^ 40 * 8174960 * 2
def baseEnd_8174960 : Nat := 4197683811279440665104049

theorem tailTrace_8174960 : CollatzResearch.WordTrace tailWord_8174960 prefixEnd_8174960 4197683811279440665104049 := by
  unfold tailWord_8174960
  simp only [CollatzResearch.WordTrace]
  refine ⟨149082643231761783429089167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198776857642349044572118889 149082643231761783429089167)
  ·
    refine ⟨223623964847642675143633751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149082643231761783429089167 223623964847642675143633751)
    ·
      refine ⟨335435947271464012715450627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223623964847642675143633751 335435947271464012715450627)
      ·
        refine ⟨503153920907196019073175941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335435947271464012715450627 503153920907196019073175941)
        ·
          refine ⟨94341360170099253576220489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 503153920907196019073175941 94341360170099253576220489)
          ·
            refine ⟨70756020127574440182165367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94341360170099253576220489 70756020127574440182165367)
            ·
              refine ⟨106134030191361660273248051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70756020127574440182165367 106134030191361660273248051)
              ·
                refine ⟨159201045287042490409872077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106134030191361660273248051 159201045287042490409872077)
                ·
                  refine ⟨59700391982640933903702029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159201045287042490409872077 59700391982640933903702029)
                  ·
                    refine ⟨22387646993490350213888261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59700391982640933903702029 22387646993490350213888261)
                    ·
                      refine ⟨4197683811279440665104049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22387646993490350213888261 4197683811279440665104049)
                      ·
                        rfl

theorem cell23_8174960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 4].length) (baseStart_8174960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174960 prefixEnd_8174960 := by exact prefixLift 8174960
  have htrace : WordTrace (prefixWord ++ tailWord_8174960) baseStart_8174960 baseEnd_8174960 := by
    simpa [prefixWord, tailWord_8174960, baseEnd_8174960] using wordTrace_append hprefix tailTrace_8174960
  have hstable : (prefixWord ++ tailWord_8174960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174960).length < 2 ^ (prefixWord ++ tailWord_8174960).sum := by decide
  have hdescent : baseEnd_8174960 < baseStart_8174960 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174978 : List Nat := [3, 4, 2, 1, 1, 3, 1, 3, 5]
def baseStart_8174978 : Nat := 118140960795 + 8174978 * 2 ^ 59
def prefixEnd_8174978 : Nat := 4983230072969 + 3 ^ 40 * 8174978 * 2
def baseEnd_8174978 : Nat := 466410339325691288297663

theorem tailTrace_8174978 : CollatzResearch.WordTrace tailWord_8174978 prefixEnd_8174978 466410339325691288297663 := by
  unfold tailWord_8174978
  simp only [CollatzResearch.WordTrace]
  refine ⟨74541485744364588983083397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198777295318305570621555725 74541485744364588983083397)
  ·
    refine ⟨13976528577068360434328137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74541485744364588983083397 13976528577068360434328137)
    ·
      refine ⟨10482396432801270325746103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13976528577068360434328137 10482396432801270325746103)
      ·
        refine ⟨15723594649201905488619155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10482396432801270325746103 15723594649201905488619155)
        ·
          refine ⟨23585391973802858232928733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15723594649201905488619155 23585391973802858232928733)
          ·
            refine ⟨8844521990176071837348275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23585391973802858232928733 8844521990176071837348275)
            ·
              refine ⟨13266782985264107756022413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8844521990176071837348275 13266782985264107756022413)
              ·
                refine ⟨4975043619474040408508405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13266782985264107756022413 4975043619474040408508405)
                ·
                  refine ⟨466410339325691288297663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4975043619474040408508405 466410339325691288297663)
                  ·
                    rfl

theorem cell23_8174978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_8174978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174978 prefixEnd_8174978 := by exact prefixLift 8174978
  have htrace : WordTrace (prefixWord ++ tailWord_8174978) baseStart_8174978 baseEnd_8174978 := by
    simpa [prefixWord, tailWord_8174978, baseEnd_8174978] using wordTrace_append hprefix tailTrace_8174978
  have hstable : (prefixWord ++ tailWord_8174978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174978).length < 2 ^ (prefixWord ++ tailWord_8174978).sum := by decide
  have hdescent : baseEnd_8174978 < baseStart_8174978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8174997 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 4, 2, 3]
def baseStart_8174997 : Nat := 118140960795 + 8174997 * 2 ^ 59
def prefixEnd_8174997 : Nat := 4983230072969 + 3 ^ 40 * 8174997 * 2
def baseEnd_8174997 : Nat := 4197702810063657020341379

theorem tailTrace_8174997 : CollatzResearch.WordTrace tailWord_8174997 prefixEnd_8174997 4197702810063657020341379 := by
  unfold tailWord_8174997
  simp only [CollatzResearch.WordTrace]
  refine ⟨298166635964389522177275245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198777757309593014784850163 298166635964389522177275245)
  ·
    refine ⟨111812488486646070816478217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298166635964389522177275245 111812488486646070816478217)
    ·
      refine ⟨83859366364984553112358663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111812488486646070816478217 83859366364984553112358663)
      ·
        refine ⟨125789049547476829668537995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83859366364984553112358663 125789049547476829668537995)
        ·
          refine ⟨188683574321215244502806993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125789049547476829668537995 188683574321215244502806993)
          ·
            refine ⟨141512680740911433377105245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188683574321215244502806993 141512680740911433377105245)
            ·
              refine ⟨53067255277841787516414467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141512680740911433377105245 53067255277841787516414467)
              ·
                refine ⟨79600882916762681274621701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53067255277841787516414467 79600882916762681274621701)
                ·
                  refine ⟨14925165546893002738991569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79600882916762681274621701 14925165546893002738991569)
                  ·
                    refine ⟨11193874160169752054243677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14925165546893002738991569 11193874160169752054243677)
                    ·
                      refine ⟨4197702810063657020341379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11193874160169752054243677 4197702810063657020341379)
                      ·
                        rfl

theorem cell23_8174997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_8174997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8174997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8174997 prefixEnd_8174997 := by exact prefixLift 8174997
  have htrace : WordTrace (prefixWord ++ tailWord_8174997) baseStart_8174997 baseEnd_8174997 := by
    simpa [prefixWord, tailWord_8174997, baseEnd_8174997] using wordTrace_append hprefix tailTrace_8174997
  have hstable : (prefixWord ++ tailWord_8174997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8174997).length < 2 ^ (prefixWord ++ tailWord_8174997).sum := by decide
  have hdescent : baseEnd_8174997 < baseStart_8174997 := by decide
  rcases family_descends (prefixWord ++ tailWord_8174997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175020 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 6]
def baseStart_8175020 : Nat := 118140960795 + 8175020 * 2 ^ 59
def prefixEnd_8175020 : Nat := 4983230072969 + 3 ^ 40 * 8175020 * 2
def baseEnd_8175020 : Nat := 4197714620118710430353773

theorem tailTrace_8175020 : CollatzResearch.WordTrace tailWord_8175020 prefixEnd_8175020 4197714620118710430353773 := by
  unfold tailWord_8175020
  simp only [CollatzResearch.WordTrace]
  refine ⟨149083737421653098552681257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198778316562204131403575009 149083737421653098552681257)
  ·
    refine ⟨111812803066239823914510943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149083737421653098552681257 111812803066239823914510943)
    ·
      refine ⟨167719204599359735871766415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111812803066239823914510943 167719204599359735871766415)
      ·
        refine ⟨251578806899039603807649623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167719204599359735871766415 251578806899039603807649623)
        ·
          refine ⟨377368210348559405711474435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251578806899039603807649623 377368210348559405711474435)
          ·
            refine ⟨566052315522839108567211653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377368210348559405711474435 566052315522839108567211653)
            ·
              refine ⟨106134809160532332856352185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 566052315522839108567211653 106134809160532332856352185)
              ·
                refine ⟨79601106870399249642264139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106134809160532332856352185 79601106870399249642264139)
                ·
                  refine ⟨119401660305598874463396209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79601106870399249642264139 119401660305598874463396209)
                  ·
                    refine ⟨89551245229199155847547157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119401660305598874463396209 89551245229199155847547157)
                    ·
                      refine ⟨4197714620118710430353773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89551245229199155847547157 4197714620118710430353773)
                      ·
                        rfl

theorem cell23_8175020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_8175020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175020 prefixEnd_8175020 := by exact prefixLift 8175020
  have htrace : WordTrace (prefixWord ++ tailWord_8175020) baseStart_8175020 baseEnd_8175020 := by
    simpa [prefixWord, tailWord_8175020, baseEnd_8175020] using wordTrace_append hprefix tailTrace_8175020
  have hstable : (prefixWord ++ tailWord_8175020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175020).length < 2 ^ (prefixWord ++ tailWord_8175020).sum := by decide
  have hdescent : baseEnd_8175020 < baseStart_8175020 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175094 : List Nat := [5, 1, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_8175094 : Nat := 118140960795 + 8175094 * 2 ^ 59
def prefixEnd_8175094 : Nat := 4983230072969 + 3 ^ 40 * 8175094 * 2
def baseEnd_8175094 : Nat := 1399250872562381046942811

theorem tailTrace_8175094 : CollatzResearch.WordTrace tailWord_8175094 prefixEnd_8175094 1399250872562381046942811 := by
  unfold tailWord_8175094
  simp only [CollatzResearch.WordTrace]
  refine ⟨18635635865314881733972271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198780115896692071829037557 18635635865314881733972271)
  ·
    refine ⟨27953453797972322600958407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18635635865314881733972271 27953453797972322600958407)
    ·
      refine ⟨41930180696958483901437611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27953453797972322600958407 41930180696958483901437611)
      ·
        refine ⟨62895271045437725852156417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41930180696958483901437611 62895271045437725852156417)
        ·
          refine ⟨47171453284078294389117313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62895271045437725852156417 47171453284078294389117313)
          ·
            refine ⟨35378589963058720791837985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47171453284078294389117313 35378589963058720791837985)
            ·
              refine ⟨26533942472294040593878489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35378589963058720791837985 26533942472294040593878489)
              ·
                refine ⟨19900456854220530445408867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26533942472294040593878489 19900456854220530445408867)
                ·
                  refine ⟨29850685281330795668113301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19900456854220530445408867 29850685281330795668113301)
                  ·
                    refine ⟨1399250872562381046942811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29850685281330795668113301 1399250872562381046942811)
                    ·
                      rfl

theorem cell23_8175094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_8175094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175094 prefixEnd_8175094 := by exact prefixLift 8175094
  have htrace : WordTrace (prefixWord ++ tailWord_8175094) baseStart_8175094 baseEnd_8175094 := by
    simpa [prefixWord, tailWord_8175094, baseEnd_8175094] using wordTrace_append hprefix tailTrace_8175094
  have hstable : (prefixWord ++ tailWord_8175094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175094).length < 2 ^ (prefixWord ++ tailWord_8175094).sum := by decide
  have hdescent : baseEnd_8175094 < baseStart_8175094 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175101 : List Nat := [1, 4, 1, 1, 1, 4, 4, 1, 1, 1, 4]
def baseStart_8175101 : Nat := 118140960795 + 8175101 * 2 ^ 59
def prefixEnd_8175101 : Nat := 4983230072969 + 3 ^ 40 * 8175101 * 2
def baseEnd_8175101 : Nat := 4197756212051724613440901

theorem tailTrace_8175101 : CollatzResearch.WordTrace tailWord_8175101 prefixEnd_8175101 4197756212051724613440901 := by
  unfold tailWord_8175101
  simp only [CollatzResearch.WordTrace]
  refine ⟨298170429156012747939061157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198780286104008498626040771 298170429156012747939061157)
  ·
    refine ⟨55906955466752390238573967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298170429156012747939061157 55906955466752390238573967)
    ·
      refine ⟨83860433200128585357860951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55906955466752390238573967 83860433200128585357860951)
      ·
        refine ⟨125790649800192878036791427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83860433200128585357860951 125790649800192878036791427)
        ·
          refine ⟨188685974700289317055187141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125790649800192878036791427 188685974700289317055187141)
          ·
            refine ⟨35378620256304246947847589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188685974700289317055187141 35378620256304246947847589)
            ·
              refine ⟨6633491298057046302721423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35378620256304246947847589 6633491298057046302721423)
              ·
                refine ⟨9950236947085569454082135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6633491298057046302721423 9950236947085569454082135)
                ·
                  refine ⟨14925355420628354181123203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9950236947085569454082135 14925355420628354181123203)
                  ·
                    refine ⟨22388033130942531271684805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14925355420628354181123203 22388033130942531271684805)
                    ·
                      refine ⟨4197756212051724613440901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22388033130942531271684805 4197756212051724613440901)
                      ·
                        rfl

theorem cell23_8175101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_8175101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175101 prefixEnd_8175101 := by exact prefixLift 8175101
  have htrace : WordTrace (prefixWord ++ tailWord_8175101) baseStart_8175101 baseEnd_8175101 := by
    simpa [prefixWord, tailWord_8175101, baseEnd_8175101] using wordTrace_append hprefix tailTrace_8175101
  have hstable : (prefixWord ++ tailWord_8175101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175101).length < 2 ^ (prefixWord ++ tailWord_8175101).sum := by decide
  have hdescent : baseEnd_8175101 < baseStart_8175101 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175111 : List Nat := [1, 1, 4, 3, 2, 1, 3, 2, 2, 4]
def baseStart_8175111 : Nat := 118140960795 + 8175111 * 2 ^ 59
def prefixEnd_8175111 : Nat := 4983230072969 + 3 ^ 40 * 8175111 * 2
def baseEnd_8175111 : Nat := 1399253782286089858105285

theorem tailTrace_8175111 : CollatzResearch.WordTrace tailWord_8175111 prefixEnd_8175111 1399253782286089858105285 := by
  unfold tailWord_8175111
  simp only [CollatzResearch.WordTrace]
  refine ⟨298170793885976519646925187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198780529257317679764616791 298170793885976519646925187)
  ·
    refine ⟨447256190828964779470387781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298170793885976519646925187 447256190828964779470387781)
    ·
      refine ⟨83860535780430896150697709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447256190828964779470387781 83860535780430896150697709)
      ·
        refine ⟨31447700917661586056511641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83860535780430896150697709 31447700917661586056511641)
        ·
          refine ⟨23585775688246189542383731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31447700917661586056511641 23585775688246189542383731)
          ·
            refine ⟨35378663532369284313575597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23585775688246189542383731 35378663532369284313575597)
            ·
              refine ⟨13266998824638481617590849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35378663532369284313575597 13266998824638481617590849)
              ·
                refine ⟨9950249118478861213193137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13266998824638481617590849 9950249118478861213193137)
                ·
                  refine ⟨7462686838859145909894853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9950249118478861213193137 7462686838859145909894853)
                  ·
                    refine ⟨1399253782286089858105285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7462686838859145909894853 1399253782286089858105285)
                    ·
                      rfl

theorem cell23_8175111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_8175111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175111 prefixEnd_8175111 := by exact prefixLift 8175111
  have htrace : WordTrace (prefixWord ++ tailWord_8175111) baseStart_8175111 baseEnd_8175111 := by
    simpa [prefixWord, tailWord_8175111, baseEnd_8175111] using wordTrace_append hprefix tailTrace_8175111
  have hstable : (prefixWord ++ tailWord_8175111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175111).length < 2 ^ (prefixWord ++ tailWord_8175111).sum := by decide
  have hdescent : baseEnd_8175111 < baseStart_8175111 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175128 : List Nat := [2, 1, 2, 3, 4, 1, 3, 1, 2, 4]
def baseStart_8175128 : Nat := 118140960795 + 8175128 * 2 ^ 59
def prefixEnd_8175128 : Nat := 4983230072969 + 3 ^ 40 * 8175128 * 2
def baseEnd_8175128 : Nat := 1399256692009798669267759

theorem tailTrace_8175128 : CollatzResearch.WordTrace tailWord_8175128 prefixEnd_8175128 1399256692009798669267759 := by
  unfold tailWord_8175128
  simp only [CollatzResearch.WordTrace]
  refine ⟨149085706963457465775147019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198780942617943287700196025 149085706963457465775147019)
  ·
    refine ⟨223628560445186198662720529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149085706963457465775147019 223628560445186198662720529)
    ·
      refine ⟨167721420333889648997040397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223628560445186198662720529 167721420333889648997040397)
      ·
        refine ⟨62895532625208618373890149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167721420333889648997040397 62895532625208618373890149)
        ·
          refine ⟨11792912367226615945104403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62895532625208618373890149 11792912367226615945104403)
          ·
            refine ⟨17689368550839923917656605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11792912367226615945104403 17689368550839923917656605)
            ·
              refine ⟨6633513206564971469121227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17689368550839923917656605 6633513206564971469121227)
              ·
                refine ⟨9950269809847457203681841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6633513206564971469121227 9950269809847457203681841)
                ·
                  refine ⟨7462702357385592902761381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9950269809847457203681841 7462702357385592902761381)
                  ·
                    refine ⟨1399256692009798669267759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7462702357385592902761381 1399256692009798669267759)
                    ·
                      rfl

theorem cell23_8175128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 2, 4].length) (baseStart_8175128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175128 prefixEnd_8175128 := by exact prefixLift 8175128
  have htrace : WordTrace (prefixWord ++ tailWord_8175128) baseStart_8175128 baseEnd_8175128 := by
    simpa [prefixWord, tailWord_8175128, baseEnd_8175128] using wordTrace_append hprefix tailTrace_8175128
  have hstable : (prefixWord ++ tailWord_8175128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175128).length < 2 ^ (prefixWord ++ tailWord_8175128).sum := by decide
  have hdescent : baseEnd_8175128 < baseStart_8175128 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175208 : List Nat := [2, 1, 4, 3, 1, 2, 1, 2, 1, 4, 2]
def baseStart_8175208 : Nat := 118140960795 + 8175208 * 2 ^ 59
def prefixEnd_8175208 : Nat := 4983230072969 + 3 ^ 40 * 8175208 * 2
def baseEnd_8175208 : Nat := 4197811154481755694802909

theorem tailTrace_8175208 : CollatzResearch.WordTrace tailWord_8175208 prefixEnd_8175208 4197811154481755694802909 := by
  unfold tailWord_8175208
  simp only [CollatzResearch.WordTrace]
  refine ⟨149087165883312552606603139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198782887844416736808804185 149087165883312552606603139)
  ·
    refine ⟨223630748824968828909904709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149087165883312552606603139 223630748824968828909904709)
    ·
      refine ⟨41930765404681655420607133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223630748824968828909904709 41930765404681655420607133)
      ·
        refine ⟨15724037026755620782727675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41930765404681655420607133 15724037026755620782727675)
        ·
          refine ⟨23586055540133431174091513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15724037026755620782727675 23586055540133431174091513)
          ·
            refine ⟨17689541655100073380568635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23586055540133431174091513 17689541655100073380568635)
            ·
              refine ⟨26534312482650110070852953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17689541655100073380568635 26534312482650110070852953)
              ·
                refine ⟨19900734361987582553139715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26534312482650110070852953 19900734361987582553139715)
                ·
                  refine ⟨29851101542981373829709573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19900734361987582553139715 29851101542981373829709573)
                  ·
                    refine ⟨5597081539309007593070545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29851101542981373829709573 5597081539309007593070545)
                    ·
                      refine ⟨4197811154481755694802909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5597081539309007593070545 4197811154481755694802909)
                      ·
                        rfl

theorem cell23_8175208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_8175208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175208 prefixEnd_8175208 := by exact prefixLift 8175208
  have htrace : WordTrace (prefixWord ++ tailWord_8175208) baseStart_8175208 baseEnd_8175208 := by
    simpa [prefixWord, tailWord_8175208, baseEnd_8175208] using wordTrace_append hprefix tailTrace_8175208
  have hstable : (prefixWord ++ tailWord_8175208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175208).length < 2 ^ (prefixWord ++ tailWord_8175208).sum := by decide
  have hdescent : baseEnd_8175208 < baseStart_8175208 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175257 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 1, 10]
def baseStart_8175257 : Nat := 118140960795 + 8175257 * 2 ^ 59
def prefixEnd_8175257 : Nat := 4983230072969 + 3 ^ 40 * 8175257 * 2
def baseEnd_8175257 : Nat := 1399278771677942001030061

theorem tailTrace_8175257 : CollatzResearch.WordTrace tailWord_8175257 prefixEnd_8175257 1399278771677942001030061 := by
  unfold tailWord_8175257
  simp only [CollatzResearch.WordTrace]
  refine ⟨298176118943447586581740025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198784079295631724387826683 298176118943447586581740025)
  ·
    refine ⟨223632089207585689936305019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298176118943447586581740025 223632089207585689936305019)
    ·
      refine ⟨335448133811378534904457529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223632089207585689936305019 335448133811378534904457529)
      ·
        refine ⟨251586100358533901178343147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335448133811378534904457529 251586100358533901178343147)
        ·
          refine ⟨377379150537800851767514721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251586100358533901178343147 377379150537800851767514721)
          ·
            refine ⟨283034362903350638825636041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377379150537800851767514721 283034362903350638825636041)
            ·
              refine ⟨212275772177512979119227031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283034362903350638825636041 212275772177512979119227031)
              ·
                refine ⟨318413658266269468678840547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212275772177512979119227031 318413658266269468678840547)
                ·
                  refine ⟨477620487399404203018260821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318413658266269468678840547 477620487399404203018260821)
                  ·
                    refine ⟨1399278771677942001030061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 477620487399404203018260821 1399278771677942001030061)
                    ·
                      rfl

theorem cell23_8175257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 10].length) (baseStart_8175257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175257 prefixEnd_8175257 := by exact prefixLift 8175257
  have htrace : WordTrace (prefixWord ++ tailWord_8175257) baseStart_8175257 baseEnd_8175257 := by
    simpa [prefixWord, tailWord_8175257, baseEnd_8175257] using wordTrace_append hprefix tailTrace_8175257
  have hstable : (prefixWord ++ tailWord_8175257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175257).length < 2 ^ (prefixWord ++ tailWord_8175257).sum := by decide
  have hdescent : baseEnd_8175257 < baseStart_8175257 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175335 : List Nat := [1, 1, 5, 4, 1, 1, 1, 2, 2, 2, 3]
def baseStart_8175335 : Nat := 118140960795 + 8175335 * 2 ^ 59
def prefixEnd_8175335 : Nat := 4983230072969 + 3 ^ 40 * 8175335 * 2
def baseEnd_8175335 : Nat := 4197876366524876697914825

theorem tailTrace_8175335 : CollatzResearch.WordTrace tailWord_8175335 prefixEnd_8175335 4197876366524876697914825 := by
  unfold tailWord_8175335
  simp only [CollatzResearch.WordTrace]
  refine ⟨298178963837165005903079459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198785975891443337268719639 298178963837165005903079459)
  ·
    refine ⟨447268445755747508854619189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298178963837165005903079459 447268445755747508854619189)
    ·
      refine ⟨41931416789601328955120549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 447268445755747508854619189 41931416789601328955120549)
      ·
        refine ⟨7862140648050249179085103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41931416789601328955120549 7862140648050249179085103)
        ·
          refine ⟨11793210972075373768627655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7862140648050249179085103 11793210972075373768627655)
          ·
            refine ⟨17689816458113060652941483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11793210972075373768627655 17689816458113060652941483)
            ·
              refine ⟨26534724687169590979412225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17689816458113060652941483 26534724687169590979412225)
              ·
                refine ⟨19901043515377193234559169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26534724687169590979412225 19901043515377193234559169)
                ·
                  refine ⟨14925782636532894925919377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19901043515377193234559169 14925782636532894925919377)
                  ·
                    refine ⟨11194336977399671194439533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14925782636532894925919377 11194336977399671194439533)
                    ·
                      refine ⟨4197876366524876697914825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11194336977399671194439533 4197876366524876697914825)
                      ·
                        rfl

theorem cell23_8175335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_8175335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175335 prefixEnd_8175335 := by exact prefixLift 8175335
  have htrace : WordTrace (prefixWord ++ tailWord_8175335) baseStart_8175335 baseEnd_8175335 := by
    simpa [prefixWord, tailWord_8175335, baseEnd_8175335] using wordTrace_append hprefix tailTrace_8175335
  have hstable : (prefixWord ++ tailWord_8175335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175335).length < 2 ^ (prefixWord ++ tailWord_8175335).sum := by decide
  have hdescent : baseEnd_8175335 < baseStart_8175335 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175354 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4]
def baseStart_8175354 : Nat := 118140960795 + 8175354 * 2 ^ 59
def prefixEnd_8175354 : Nat := 4983230072969 + 3 ^ 40 * 8175354 * 2
def baseEnd_8175354 : Nat := 4197886122657312123577237

theorem tailTrace_8175354 : CollatzResearch.WordTrace tailWord_8175354 prefixEnd_8175354 4197886122657312123577237 := by
  unfold tailWord_8175354
  simp only [CollatzResearch.WordTrace]
  refine ⟨74544914206024043037005279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198786437882730781432014077 74544914206024043037005279)
  ·
    refine ⟨111817371309036064555507919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74544914206024043037005279 111817371309036064555507919)
    ·
      refine ⟨167726056963554096833261879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111817371309036064555507919 167726056963554096833261879)
      ·
        refine ⟨251589085445331145249892819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167726056963554096833261879 251589085445331145249892819)
        ·
          refine ⟨377383628167996717874839229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251589085445331145249892819 377383628167996717874839229)
          ·
            refine ⟨141518860562998769203064711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377383628167996717874839229 141518860562998769203064711)
            ·
              refine ⟨212278290844498153804597067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141518860562998769203064711 212278290844498153804597067)
              ·
                refine ⟨318417436266747230706895601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212278290844498153804597067 318417436266747230706895601)
                ·
                  refine ⟨238813077200060423030171701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318417436266747230706895601 238813077200060423030171701)
                  ·
                    refine ⟨22388725987505664659078597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 238813077200060423030171701 22388725987505664659078597)
                    ·
                      refine ⟨4197886122657312123577237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22388725987505664659078597 4197886122657312123577237)
                      ·
                        rfl

theorem cell23_8175354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_8175354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175354 prefixEnd_8175354 := by exact prefixLift 8175354
  have htrace : WordTrace (prefixWord ++ tailWord_8175354) baseStart_8175354 baseEnd_8175354 := by
    simpa [prefixWord, tailWord_8175354, baseEnd_8175354] using wordTrace_append hprefix tailTrace_8175354
  have hstable : (prefixWord ++ tailWord_8175354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175354).length < 2 ^ (prefixWord ++ tailWord_8175354).sum := by decide
  have hdescent : baseEnd_8175354 < baseStart_8175354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175366 : List Nat := [6, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_8175366 : Nat := 118140960795 + 8175366 * 2 ^ 59
def prefixEnd_8175366 : Nat := 4983230072969 + 3 ^ 40 * 8175366 * 2
def baseEnd_8175366 : Nat := 4197892284425166076627183

theorem tailTrace_8175366 : CollatzResearch.WordTrace tailWord_8175366 prefixEnd_8175366 4197892284425166076627183 := by
  unfold tailWord_8175366
  simp only [CollatzResearch.WordTrace]
  refine ⟨9318127953126646818670561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 198786729666701798798305301 9318127953126646818670561)
  ·
    refine ⟨6988595964844985114002921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9318127953126646818670561 6988595964844985114002921)
    ·
      refine ⟨5241446973633738835502191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6988595964844985114002921 5241446973633738835502191)
      ·
        refine ⟨7862170460450608253253287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5241446973633738835502191 7862170460450608253253287)
        ·
          refine ⟨11793255690675912379879931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7862170460450608253253287 11793255690675912379879931)
          ·
            refine ⟨17689883536013868569819897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11793255690675912379879931 17689883536013868569819897)
            ·
              refine ⟨13267412652010401427364923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17689883536013868569819897 13267412652010401427364923)
              ·
                refine ⟨19901118978015602141047385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13267412652010401427364923 19901118978015602141047385)
                ·
                  refine ⟨14925839233511701605785539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19901118978015602141047385 14925839233511701605785539)
                  ·
                    refine ⟨22388758850267552408678309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14925839233511701605785539 22388758850267552408678309)
                    ·
                      refine ⟨4197892284425166076627183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22388758850267552408678309 4197892284425166076627183)
                      ·
                        rfl

theorem cell23_8175366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_8175366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175366 prefixEnd_8175366 := by exact prefixLift 8175366
  have htrace : WordTrace (prefixWord ++ tailWord_8175366) baseStart_8175366 baseEnd_8175366 := by
    simpa [prefixWord, tailWord_8175366, baseEnd_8175366] using wordTrace_append hprefix tailTrace_8175366
  have hstable : (prefixWord ++ tailWord_8175366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175366).length < 2 ^ (prefixWord ++ tailWord_8175366).sum := by decide
  have hdescent : baseEnd_8175366 < baseStart_8175366 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175371 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 2, 6, 2]
def baseStart_8175371 : Nat := 118140960795 + 8175371 * 2 ^ 59
def prefixEnd_8175371 : Nat := 4983230072969 + 3 ^ 40 * 8175371 * 2
def baseEnd_8175371 : Nat := 4197894851828438557064659

theorem tailTrace_8175371 : CollatzResearch.WordTrace tailWord_8175371 prefixEnd_8175371 4197894851828438557064659 := by
  unfold tailWord_8175371
  simp only [CollatzResearch.WordTrace]
  refine ⟨298180276865034584051389967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198786851243356389367593311 298180276865034584051389967)
  ·
    refine ⟨447270415297551876077084951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298180276865034584051389967 447270415297551876077084951)
    ·
      refine ⟨670905622946327814115627427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447270415297551876077084951 670905622946327814115627427)
      ·
        refine ⟨1006358434419491721173441141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670905622946327814115627427 1006358434419491721173441141)
        ·
          refine ⟨94346103226827348860010107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1006358434419491721173441141 94346103226827348860010107)
          ·
            refine ⟨141519154840241023290015161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94346103226827348860010107 141519154840241023290015161)
            ·
              refine ⟨106139366130180767467511371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141519154840241023290015161 106139366130180767467511371)
              ·
                refine ⟨159209049195271151201267057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106139366130180767467511371 159209049195271151201267057)
                ·
                  refine ⟨119406786896453363400950293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159209049195271151201267057 119406786896453363400950293)
                  ·
                    refine ⟨5597193135771251409419545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119406786896453363400950293 5597193135771251409419545)
                    ·
                      refine ⟨4197894851828438557064659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5597193135771251409419545 4197894851828438557064659)
                      ·
                        rfl

theorem cell23_8175371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 6, 2].length) (baseStart_8175371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175371 prefixEnd_8175371 := by exact prefixLift 8175371
  have htrace : WordTrace (prefixWord ++ tailWord_8175371) baseStart_8175371 baseEnd_8175371 := by
    simpa [prefixWord, tailWord_8175371, baseEnd_8175371] using wordTrace_append hprefix tailTrace_8175371
  have hstable : (prefixWord ++ tailWord_8175371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175371).length < 2 ^ (prefixWord ++ tailWord_8175371).sum := by decide
  have hdescent : baseEnd_8175371 < baseStart_8175371 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175381 : List Nat := [1, 3, 2, 1, 2, 4, 1, 2, 1, 6]
def baseStart_8175381 : Nat := 118140960795 + 8175381 * 2 ^ 59
def prefixEnd_8175381 : Nat := 4983230072969 + 3 ^ 40 * 8175381 * 2
def baseEnd_8175381 : Nat := 1399299995544994505979871

theorem tailTrace_8175381 : CollatzResearch.WordTrace tailWord_8175381 prefixEnd_8175381 1399299995544994505979871 := by
  unfold tailWord_8175381
  simp only [CollatzResearch.WordTrace]
  refine ⟨298180641594998355759253997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198787094396665570506169331 298180641594998355759253997)
  ·
    refine ⟨111817740598124383409720249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298180641594998355759253997 111817740598124383409720249)
    ·
      refine ⟨83863305448593287557290187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111817740598124383409720249 83863305448593287557290187)
      ·
        refine ⟨125794958172889931335935281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83863305448593287557290187 125794958172889931335935281)
        ·
          refine ⟨94346218629667448501951461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125794958172889931335935281 94346218629667448501951461)
          ·
            refine ⟨17689915993062646594115899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94346218629667448501951461 17689915993062646594115899)
            ·
              refine ⟨26534873989593969891173849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17689915993062646594115899 26534873989593969891173849)
              ·
                refine ⟨19901155492195477418380387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26534873989593969891173849 19901155492195477418380387)
                ·
                  refine ⟨29851733238293216127570581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19901155492195477418380387 29851733238293216127570581)
                  ·
                    refine ⟨1399299995544994505979871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29851733238293216127570581 1399299995544994505979871)
                    ·
                      rfl

theorem cell23_8175381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_8175381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175381 prefixEnd_8175381 := by exact prefixLift 8175381
  have htrace : WordTrace (prefixWord ++ tailWord_8175381) baseStart_8175381 baseEnd_8175381 := by
    simpa [prefixWord, tailWord_8175381, baseEnd_8175381] using wordTrace_append hprefix tailTrace_8175381
  have hstable : (prefixWord ++ tailWord_8175381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175381).length < 2 ^ (prefixWord ++ tailWord_8175381).sum := by decide
  have hdescent : baseEnd_8175381 < baseStart_8175381 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175418 : List Nat := [3, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4]
def baseStart_8175418 : Nat := 118140960795 + 8175418 * 2 ^ 59
def prefixEnd_8175418 : Nat := 4983230072969 + 3 ^ 40 * 8175418 * 2
def baseEnd_8175418 : Nat := 4197918985419199873176943

theorem tailTrace_8175418 : CollatzResearch.WordTrace tailWord_8175418 prefixEnd_8175418 4197918985419199873176943 := by
  unfold tailWord_8175418
  simp only [CollatzResearch.WordTrace]
  refine ⟨74545497773966077769587727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198787994063909540718900605 74545497773966077769587727)
  ·
    refine ⟨111818246660949116654381591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74545497773966077769587727 111818246660949116654381591)
    ·
      refine ⟨167727369991423674981572387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111818246660949116654381591 167727369991423674981572387)
      ·
        refine ⟨251591054987135512472358581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167727369991423674981572387 251591054987135512472358581)
        ·
          refine ⟨23586661405043954294283617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 251591054987135512472358581 23586661405043954294283617)
          ·
            refine ⟨17689996053782965720712713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23586661405043954294283617 17689996053782965720712713)
            ·
              refine ⟨13267497040337224290534535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17689996053782965720712713 13267497040337224290534535)
              ·
                refine ⟨19901245560505836435801803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13267497040337224290534535 19901245560505836435801803)
                ·
                  refine ⟨29851868340758754653702705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19901245560505836435801803 29851868340758754653702705)
                  ·
                    refine ⟨22388901255569065990277029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29851868340758754653702705 22388901255569065990277029)
                    ·
                      refine ⟨4197918985419199873176943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22388901255569065990277029 4197918985419199873176943)
                      ·
                        rfl

theorem cell23_8175418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_8175418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175418 prefixEnd_8175418 := by exact prefixLift 8175418
  have htrace : WordTrace (prefixWord ++ tailWord_8175418) baseStart_8175418 baseEnd_8175418 := by
    simpa [prefixWord, tailWord_8175418, baseEnd_8175418] using wordTrace_append hprefix tailTrace_8175418
  have hstable : (prefixWord ++ tailWord_8175418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175418).length < 2 ^ (prefixWord ++ tailWord_8175418).sum := by decide
  have hdescent : baseEnd_8175418 < baseStart_8175418 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175422 : List Nat := [4, 2, 1, 2, 2, 2, 1, 2, 3, 2, 2]
def baseStart_8175422 : Nat := 118140960795 + 8175422 * 2 ^ 59
def prefixEnd_8175422 : Nat := 4983230072969 + 3 ^ 40 * 8175422 * 2
def baseEnd_8175422 : Nat := 4197921039341817857526925

theorem tailTrace_8175422 : CollatzResearch.WordTrace tailWord_8175422 prefixEnd_8175422 4197921039341817857526925 := by
  unfold tailWord_8175422
  simp only [CollatzResearch.WordTrace]
  refine ⟨37272767123481227470187065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198788091325233213174331013 37272767123481227470187065)
  ·
    refine ⟨27954575342610920602640299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37272767123481227470187065 27954575342610920602640299)
    ·
      refine ⟨41931863013916380903960449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27954575342610920602640299 41931863013916380903960449)
      ·
        refine ⟨31448897260437285677970337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41931863013916380903960449 31448897260437285677970337)
        ·
          refine ⟨23586672945327964258477753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31448897260437285677970337 23586672945327964258477753)
          ·
            refine ⟨17690004708995973193858315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23586672945327964258477753 17690004708995973193858315)
            ·
              refine ⟨26535007063493959790787473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17690004708995973193858315 26535007063493959790787473)
              ·
                refine ⟨19901255297620469843090605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26535007063493959790787473 19901255297620469843090605)
                ·
                  refine ⟨7462970736607676191158977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19901255297620469843090605 7462970736607676191158977)
                  ·
                    refine ⟨5597228052455757143369233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7462970736607676191158977 5597228052455757143369233)
                    ·
                      refine ⟨4197921039341817857526925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5597228052455757143369233 4197921039341817857526925)
                      ·
                        rfl

theorem cell23_8175422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_8175422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175422 prefixEnd_8175422 := by exact prefixLift 8175422
  have htrace : WordTrace (prefixWord ++ tailWord_8175422) baseStart_8175422 baseEnd_8175422 := by
    simpa [prefixWord, tailWord_8175422, baseEnd_8175422] using wordTrace_append hprefix tailTrace_8175422
  have hstable : (prefixWord ++ tailWord_8175422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175422).length < 2 ^ (prefixWord ++ tailWord_8175422).sum := by decide
  have hdescent : baseEnd_8175422 < baseStart_8175422 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175442 : List Nat := [3, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3]
def baseStart_8175442 : Nat := 118140960795 + 8175442 * 2 ^ 59
def prefixEnd_8175442 : Nat := 4983230072969 + 3 ^ 40 * 8175442 * 2
def baseEnd_8175442 : Nat := 4197931308954907779276833

theorem tailTrace_8175442 : CollatzResearch.WordTrace tailWord_8175442 prefixEnd_8175442 4197931308954907779276833 := by
  unfold tailWord_8175442
  simp only [CollatzResearch.WordTrace]
  refine ⟨74545716611944340794306145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198788577631851575451483053 74545716611944340794306145)
  ·
    refine ⟨55909287458958255595729609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74545716611944340794306145 55909287458958255595729609)
    ·
      refine ⟨41931965594218691696797207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55909287458958255595729609 41931965594218691696797207)
      ·
        refine ⟨62897948391328037545195811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41931965594218691696797207 62897948391328037545195811)
        ·
          refine ⟨94346922586992056317793717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62897948391328037545195811 94346922586992056317793717)
          ·
            refine ⟨8845023992530505279793161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94346922586992056317793717 8845023992530505279793161)
            ·
              refine ⟨6633767994397878959844871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8845023992530505279793161 6633767994397878959844871)
              ·
                refine ⟨9950651991596818439767307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6633767994397878959844871 9950651991596818439767307)
                ·
                  refine ⟨14925977987395227659650961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9950651991596818439767307 14925977987395227659650961)
                  ·
                    refine ⟨11194483490546420744738221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14925977987395227659650961 11194483490546420744738221)
                    ·
                      refine ⟨4197931308954907779276833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11194483490546420744738221 4197931308954907779276833)
                      ·
                        rfl

theorem cell23_8175442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_8175442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175442 prefixEnd_8175442 := by exact prefixLift 8175442
  have htrace : WordTrace (prefixWord ++ tailWord_8175442) baseStart_8175442 baseEnd_8175442 := by
    simpa [prefixWord, tailWord_8175442, baseEnd_8175442] using wordTrace_append hprefix tailTrace_8175442
  have hstable : (prefixWord ++ tailWord_8175442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175442).length < 2 ^ (prefixWord ++ tailWord_8175442).sum := by decide
  have hdescent : baseEnd_8175442 < baseStart_8175442 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175455 : List Nat := [1, 1, 2, 3, 1, 4, 3, 2, 2, 1, 3]
def baseStart_8175455 : Nat := 118140960795 + 8175455 * 2 ^ 59
def prefixEnd_8175455 : Nat := 4983230072969 + 3 ^ 40 * 8175455 * 2
def baseEnd_8175455 : Nat := 4197937984203416228414273

theorem tailTrace_8175455 : CollatzResearch.WordTrace tailWord_8175455 prefixEnd_8175455 4197937984203416228414273 := by
  unfold tailWord_8175455
  simp only [CollatzResearch.WordTrace]
  refine ⟨298183340596730266397447819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198788893731153510931631879 298183340596730266397447819)
  ·
    refine ⟨447275010895095399596171729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298183340596730266397447819 447275010895095399596171729)
    ·
      refine ⟨335456258171321549697128797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447275010895095399596171729 335456258171321549697128797)
      ·
        refine ⟨125796096814245581136423299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335456258171321549697128797 125796096814245581136423299)
        ·
          refine ⟨188694145221368371704634949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125796096814245581136423299 188694145221368371704634949)
          ·
            refine ⟨35380152229006569694619053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188694145221368371704634949 35380152229006569694619053)
            ·
              refine ⟨13267557085877463635482145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35380152229006569694619053 13267557085877463635482145)
              ·
                refine ⟨9950667814408097726611609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13267557085877463635482145 9950667814408097726611609)
                ·
                  refine ⟨7463000860806073294958707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9950667814408097726611609 7463000860806073294958707)
                  ·
                    refine ⟨11194501291209109942438061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7463000860806073294958707 11194501291209109942438061)
                    ·
                      refine ⟨4197937984203416228414273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11194501291209109942438061 4197937984203416228414273)
                      ·
                        rfl

theorem cell23_8175455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_8175455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175455 prefixEnd_8175455 := by exact prefixLift 8175455
  have htrace : WordTrace (prefixWord ++ tailWord_8175455) baseStart_8175455 baseEnd_8175455 := by
    simpa [prefixWord, tailWord_8175455, baseEnd_8175455] using wordTrace_append hprefix tailTrace_8175455
  have hstable : (prefixWord ++ tailWord_8175455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175455).length < 2 ^ (prefixWord ++ tailWord_8175455).sum := by decide
  have hdescent : baseEnd_8175455 < baseStart_8175455 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175481 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 2, 1, 5]
def baseStart_8175481 : Nat := 118140960795 + 8175481 * 2 ^ 59
def prefixEnd_8175481 : Nat := 4983230072969 + 3 ^ 40 * 8175481 * 2
def baseEnd_8175481 : Nat := 4197951334700433126689153

theorem tailTrace_8175481 : CollatzResearch.WordTrace tailWord_8175481 prefixEnd_8175481 4197951334700433126689153 := by
  unfold tailWord_8175481
  simp only [CollatzResearch.WordTrace]
  refine ⟨298184288894636072837894297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198789525929757381891929531 298184288894636072837894297)
  ·
    refine ⟨223638216670977054628420723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298184288894636072837894297 223638216670977054628420723)
    ·
      refine ⟨335457325006465581942631085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223638216670977054628420723 335457325006465581942631085)
      ·
        refine ⟨125796496877424593228486657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335457325006465581942631085 125796496877424593228486657)
        ·
          refine ⟨94347372658068444921364993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125796496877424593228486657 94347372658068444921364993)
          ·
            refine ⟨70760529493551333691023745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94347372658068444921364993 70760529493551333691023745)
            ·
              refine ⟨53070397120163500268267809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70760529493551333691023745 53070397120163500268267809)
              ·
                refine ⟨39802797840122625201200857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53070397120163500268267809 39802797840122625201200857)
                ·
                  refine ⟨29852098380091968900900643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39802797840122625201200857 29852098380091968900900643)
                  ·
                    refine ⟨44778147570137953351350965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29852098380091968900900643 44778147570137953351350965)
                    ·
                      refine ⟨4197951334700433126689153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44778147570137953351350965 4197951334700433126689153)
                      ·
                        rfl

theorem cell23_8175481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_8175481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175481 prefixEnd_8175481 := by exact prefixLift 8175481
  have htrace : WordTrace (prefixWord ++ tailWord_8175481) baseStart_8175481 baseEnd_8175481 := by
    simpa [prefixWord, tailWord_8175481, baseEnd_8175481] using wordTrace_append hprefix tailTrace_8175481
  have hstable : (prefixWord ++ tailWord_8175481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175481).length < 2 ^ (prefixWord ++ tailWord_8175481).sum := by decide
  have hdescent : baseEnd_8175481 < baseStart_8175481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175568 : List Nat := [2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 4]
def baseStart_8175568 : Nat := 118140960795 + 8175568 * 2 ^ 59
def prefixEnd_8175568 : Nat := 4983230072969 + 3 ^ 40 * 8175568 * 2
def baseEnd_8175568 : Nat := 4197996007517374286301253

theorem tailTrace_8175568 : CollatzResearch.WordTrace tailWord_8175568 prefixEnd_8175568 4197996007517374286301253 := by
  unfold tailWord_8175568
  simp only [CollatzResearch.WordTrace]
  refine ⟨149093731022660443348155679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198791641363547257797540905 149093731022660443348155679)
  ·
    refine ⟨223640596533990665022233519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149093731022660443348155679 223640596533990665022233519)
    ·
      refine ⟨335460894800985997533350279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223640596533990665022233519 335460894800985997533350279)
      ·
        refine ⟨503191342201478996300025419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335460894800985997533350279 503191342201478996300025419)
        ·
          refine ⟨754787013302218494450038129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503191342201478996300025419 754787013302218494450038129)
          ·
            refine ⟨566090259976663870837528597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 754787013302218494450038129 566090259976663870837528597)
            ·
              refine ⟨26535480936406118945509153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 566090259976663870837528597 26535480936406118945509153)
              ·
                refine ⟨19901610702304589209131865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26535480936406118945509153 19901610702304589209131865)
                ·
                  refine ⟨14926208026728441906848899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19901610702304589209131865 14926208026728441906848899)
                  ·
                    refine ⟨22389312040092662860273349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14926208026728441906848899 22389312040092662860273349)
                    ·
                      refine ⟨4197996007517374286301253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22389312040092662860273349 4197996007517374286301253)
                      ·
                        rfl

theorem cell23_8175568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 4].length) (baseStart_8175568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175568 prefixEnd_8175568 := by exact prefixLift 8175568
  have htrace : WordTrace (prefixWord ++ tailWord_8175568) baseStart_8175568 baseEnd_8175568 := by
    simpa [prefixWord, tailWord_8175568, baseEnd_8175568] using wordTrace_append hprefix tailTrace_8175568
  have hstable : (prefixWord ++ tailWord_8175568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175568).length < 2 ^ (prefixWord ++ tailWord_8175568).sum := by decide
  have hdescent : baseEnd_8175568 < baseStart_8175568 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175588 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 1, 4, 3]
def baseStart_8175588 : Nat := 118140960795 + 8175588 * 2 ^ 59
def prefixEnd_8175588 : Nat := 4983230072969 + 3 ^ 40 * 8175588 * 2
def baseEnd_8175588 : Nat := 4198006277130464208051161

theorem tailTrace_8175588 : CollatzResearch.WordTrace tailWord_8175588 prefixEnd_8175588 4198006277130464208051161 := by
  unfold tailWord_8175588
  simp only [CollatzResearch.WordTrace]
  refine ⟨149094095752624215056019709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198792127670165620074692945 149094095752624215056019709)
  ·
    refine ⟨55910285907234080646007391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149094095752624215056019709 55910285907234080646007391)
    ·
      refine ⟨83865428860851120969011087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55910285907234080646007391 83865428860851120969011087)
      ·
        refine ⟨125798143291276681453516631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83865428860851120969011087 125798143291276681453516631)
        ·
          refine ⟨188697214936915022180274947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125798143291276681453516631 188697214936915022180274947)
          ·
            refine ⟨283045822405372533270412421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188697214936915022180274947 283045822405372533270412421)
            ·
              refine ⟨53071091701007349988202329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 283045822405372533270412421 53071091701007349988202329)
              ·
                refine ⟨39803318775755512491151747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53071091701007349988202329 39803318775755512491151747)
                ·
                  refine ⟨59704978163633268736727621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39803318775755512491151747 59704978163633268736727621)
                  ·
                    refine ⟨11194683405681237888136429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59704978163633268736727621 11194683405681237888136429)
                    ·
                      refine ⟨4198006277130464208051161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11194683405681237888136429 4198006277130464208051161)
                      ·
                        rfl

theorem cell23_8175588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_8175588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175588 prefixEnd_8175588 := by exact prefixLift 8175588
  have htrace : WordTrace (prefixWord ++ tailWord_8175588) baseStart_8175588 baseEnd_8175588 := by
    simpa [prefixWord, tailWord_8175588, baseEnd_8175588] using wordTrace_append hprefix tailTrace_8175588
  have hstable : (prefixWord ++ tailWord_8175588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175588).length < 2 ^ (prefixWord ++ tailWord_8175588).sum := by decide
  have hdescent : baseEnd_8175588 < baseStart_8175588 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175612 : List Nat := [2, 2, 2, 1, 2, 2, 4, 3, 1, 4]
def baseStart_8175612 : Nat := 118140960795 + 8175612 * 2 ^ 59
def prefixEnd_8175612 : Nat := 4983230072969 + 3 ^ 40 * 8175612 * 2
def baseEnd_8175612 : Nat := 1399339533555390704717017

theorem tailTrace_8175612 : CollatzResearch.WordTrace tailWord_8175612 prefixEnd_8175612 1399339533555390704717017 := by
  unfold tailWord_8175612
  simp only [CollatzResearch.WordTrace]
  refine ⟨149094533428580741105456545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198792711238107654807275393 149094533428580741105456545)
  ·
    refine ⟨111820900071435555829092409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149094533428580741105456545 111820900071435555829092409)
    ·
      refine ⟨83865675053576666871819307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111820900071435555829092409 83865675053576666871819307)
      ·
        refine ⟨125798512580365000307728961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83865675053576666871819307 125798512580365000307728961)
        ·
          refine ⟨94348884435273750230796721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125798512580365000307728961 94348884435273750230796721)
          ·
            refine ⟨70761663326455312673097541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94348884435273750230796721 70761663326455312673097541)
            ·
              refine ⟨13267811873710371126205789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70761663326455312673097541 13267811873710371126205789)
              ·
                refine ⟨4975429452641389172327171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13267811873710371126205789 4975429452641389172327171)
                ·
                  refine ⟨7463144178962083758490757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4975429452641389172327171 7463144178962083758490757)
                  ·
                    refine ⟨1399339533555390704717017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7463144178962083758490757 1399339533555390704717017)
                    ·
                      rfl

theorem cell23_8175612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_8175612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175612 prefixEnd_8175612 := by exact prefixLift 8175612
  have htrace : WordTrace (prefixWord ++ tailWord_8175612) baseStart_8175612 baseEnd_8175612 := by
    simpa [prefixWord, tailWord_8175612, baseEnd_8175612] using wordTrace_append hprefix tailTrace_8175612
  have hstable : (prefixWord ++ tailWord_8175612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175612).length < 2 ^ (prefixWord ++ tailWord_8175612).sum := by decide
  have hdescent : baseEnd_8175612 < baseStart_8175612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175635 : List Nat := [1, 1, 1, 2, 1, 4, 3, 3, 3, 1, 3]
def baseStart_8175635 : Nat := 118140960795 + 8175635 * 2 ^ 59
def prefixEnd_8175635 : Nat := 4983230072969 + 3 ^ 40 * 8175635 * 2
def baseEnd_8175635 : Nat := 4198030410721225524163445

theorem tailTrace_8175635 : CollatzResearch.WordTrace tailWord_8175635 prefixEnd_8175635 4198030410721225524163445 := by
  unfold tailWord_8175635
  simp only [CollatzResearch.WordTrace]
  refine ⟨298189905736078157139000359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198793270490718771426000239 298189905736078157139000359)
  ·
    refine ⟨447284858604117235708500539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298189905736078157139000359 447284858604117235708500539)
    ·
      refine ⟨670927287906175853562750809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447284858604117235708500539 670927287906175853562750809)
      ·
        refine ⟨503195465929631890172063107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670927287906175853562750809 503195465929631890172063107)
        ·
          refine ⟨754793198894447835258094661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503195465929631890172063107 754793198894447835258094661)
          ·
            refine ⟨141523724792708969110892749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 754793198894447835258094661 141523724792708969110892749)
            ·
              refine ⟨53071396797265863416584781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141523724792708969110892749 53071396797265863416584781)
              ·
                refine ⟨19901773798974698781219293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53071396797265863416584781 19901773798974698781219293)
                ·
                  refine ⟨7463165174615512042957235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19901773798974698781219293 7463165174615512042957235)
                  ·
                    refine ⟨11194747761923268064435853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7463165174615512042957235 11194747761923268064435853)
                    ·
                      refine ⟨4198030410721225524163445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11194747761923268064435853 4198030410721225524163445)
                      ·
                        rfl

theorem cell23_8175635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 1, 3].length) (baseStart_8175635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175635 prefixEnd_8175635 := by exact prefixLift 8175635
  have htrace : WordTrace (prefixWord ++ tailWord_8175635) baseStart_8175635 baseEnd_8175635 := by
    simpa [prefixWord, tailWord_8175635, baseEnd_8175635] using wordTrace_append hprefix tailTrace_8175635
  have hstable : (prefixWord ++ tailWord_8175635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175635).length < 2 ^ (prefixWord ++ tailWord_8175635).sum := by decide
  have hdescent : baseEnd_8175635 < baseStart_8175635 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175662 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_8175662 : Nat := 118140960795 + 8175662 * 2 ^ 59
def prefixEnd_8175662 : Nat := 4983230072969 + 3 ^ 40 * 8175662 * 2
def baseEnd_8175662 : Nat := 4198044274698896918525821

theorem tailTrace_8175662 : CollatzResearch.WordTrace tailWord_8175662 prefixEnd_8175662 4198044274698896918525821 := by
  unfold tailWord_8175662
  simp only [CollatzResearch.WordTrace]
  refine ⟨37273861313372542593779155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198793927004653560500155493 37273861313372542593779155)
  ·
    refine ⟨55910791970058813890668733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37273861313372542593779155 55910791970058813890668733)
    ·
      refine ⟨20966546988772055209000775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55910791970058813890668733 20966546988772055209000775)
      ·
        refine ⟨31449820483158082813501163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20966546988772055209000775 31449820483158082813501163)
        ·
          refine ⟨47174730724737124220251745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31449820483158082813501163 47174730724737124220251745)
          ·
            refine ⟨35381048043552843165188809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47174730724737124220251745 35381048043552843165188809)
            ·
              refine ⟨26535786032664632373891607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35381048043552843165188809 26535786032664632373891607)
              ·
                refine ⟨39803679048996948560837411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26535786032664632373891607 39803679048996948560837411)
                ·
                  refine ⟨59705518573495422841256117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39803679048996948560837411 59705518573495422841256117)
                  ·
                    refine ⟨5597392366265195891367761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59705518573495422841256117 5597392366265195891367761)
                    ·
                      refine ⟨4198044274698896918525821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5597392366265195891367761 4198044274698896918525821)
                      ·
                        rfl

theorem cell23_8175662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_8175662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175662 prefixEnd_8175662 := by exact prefixLift 8175662
  have htrace : WordTrace (prefixWord ++ tailWord_8175662) baseStart_8175662 baseEnd_8175662 := by
    simpa [prefixWord, tailWord_8175662, baseEnd_8175662] using wordTrace_append hprefix tailTrace_8175662
  have hstable : (prefixWord ++ tailWord_8175662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175662).length < 2 ^ (prefixWord ++ tailWord_8175662).sum := by decide
  have hdescent : baseEnd_8175662 < baseStart_8175662 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175669 : List Nat := [1, 3, 3, 1, 1, 1, 5, 3, 1, 1, 3]
def baseStart_8175669 : Nat := 118140960795 + 8175669 * 2 ^ 59
def prefixEnd_8175669 : Nat := 4983230072969 + 3 ^ 40 * 8175669 * 2
def baseEnd_8175669 : Nat := 4198047869063478391138289

theorem tailTrace_8175669 : CollatzResearch.WordTrace tailWord_8175669 prefixEnd_8175669 4198047869063478391138289 := by
  unfold tailWord_8175669
  simp only [CollatzResearch.WordTrace]
  refine ⟨298191145817954980945738061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198794097211969987297158707 298191145817954980945738061)
  ·
    refine ⟨111821679681733117854651773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298191145817954980945738061 111821679681733117854651773)
    ·
      refine ⟨41933129880649919195494415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111821679681733117854651773 41933129880649919195494415)
      ·
        refine ⟨62899694820974878793241623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41933129880649919195494415 62899694820974878793241623)
        ·
          refine ⟨94349542231462318189862435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62899694820974878793241623 94349542231462318189862435)
          ·
            refine ⟨141524313347193477284793653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94349542231462318189862435 141524313347193477284793653)
            ·
              refine ⟨13267904376299388495449405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141524313347193477284793653 13267904376299388495449405)
              ·
                refine ⟨4975464141112270685793527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13267904376299388495449405 4975464141112270685793527)
                ·
                  refine ⟨7463196211668406028690291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4975464141112270685793527 7463196211668406028690291)
                  ·
                    refine ⟨11194794317502609043035437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7463196211668406028690291 11194794317502609043035437)
                    ·
                      refine ⟨4198047869063478391138289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11194794317502609043035437 4198047869063478391138289)
                      ·
                        rfl

theorem cell23_8175669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_8175669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175669 prefixEnd_8175669 := by exact prefixLift 8175669
  have htrace : WordTrace (prefixWord ++ tailWord_8175669) baseStart_8175669 baseEnd_8175669 := by
    simpa [prefixWord, tailWord_8175669, baseEnd_8175669] using wordTrace_append hprefix tailTrace_8175669
  have hstable : (prefixWord ++ tailWord_8175669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175669).length < 2 ^ (prefixWord ++ tailWord_8175669).sum := by decide
  have hdescent : baseEnd_8175669 < baseStart_8175669 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175685 : List Nat := [1, 3, 1, 1, 1, 3, 1, 6, 2, 4]
def baseStart_8175685 : Nat := 118140960795 + 8175685 * 2 ^ 59
def prefixEnd_8175685 : Nat := 4983230072969 + 3 ^ 40 * 8175685 * 2
def baseEnd_8175685 : Nat := 1399352028251316776179405

theorem tailTrace_8175685 : CollatzResearch.WordTrace tailWord_8175685 prefixEnd_8175685 1399352028251316776179405 := by
  unfold tailWord_8175685
  simp only [CollatzResearch.WordTrace]
  refine ⟨298191729385897015678320509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198794486257264677118880339 298191729385897015678320509)
  ·
    refine ⟨111821898519711380879370191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298191729385897015678320509 111821898519711380879370191)
    ·
      refine ⟨167732847779567071319055287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111821898519711380879370191 167732847779567071319055287)
      ·
        refine ⟨251599271669350606978582931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167732847779567071319055287 251599271669350606978582931)
        ·
          refine ⟨377398907504025910467874397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251599271669350606978582931 377398907504025910467874397)
          ·
            refine ⟨141524590314009716425452899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377398907504025910467874397 141524590314009716425452899)
            ·
              refine ⟨212286885471014574638179349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141524590314009716425452899 212286885471014574638179349)
              ·
                refine ⟨9950947756453808186164657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 212286885471014574638179349 9950947756453808186164657)
                ·
                  refine ⟨7463210817340356139623493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9950947756453808186164657 7463210817340356139623493)
                  ·
                    refine ⟨1399352028251316776179405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7463210817340356139623493 1399352028251316776179405)
                    ·
                      rfl

theorem cell23_8175685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 4].length) (baseStart_8175685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175685 prefixEnd_8175685 := by exact prefixLift 8175685
  have htrace : WordTrace (prefixWord ++ tailWord_8175685) baseStart_8175685 baseEnd_8175685 := by
    simpa [prefixWord, tailWord_8175685, baseEnd_8175685] using wordTrace_append hprefix tailTrace_8175685
  have hstable : (prefixWord ++ tailWord_8175685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175685).length < 2 ^ (prefixWord ++ tailWord_8175685).sum := by decide
  have hdescent : baseEnd_8175685 < baseStart_8175685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175688 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_8175688 : Nat := 118140960795 + 8175688 * 2 ^ 59
def prefixEnd_8175688 : Nat := 4983230072969 + 3 ^ 40 * 8175688 * 2
def baseEnd_8175688 : Nat := 4198057625195913816800701

theorem tailTrace_8175688 : CollatzResearch.WordTrace tailWord_8175688 prefixEnd_8175688 4198057625195913816800701 := by
  unfold tailWord_8175688
  simp only [CollatzResearch.WordTrace]
  refine ⟨149095919402443073595339859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198794559203257431460453145 149095919402443073595339859)
  ·
    refine ⟨223643879103664610393009789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149095919402443073595339859 223643879103664610393009789)
    ·
      refine ⟨83866454663874228897378671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223643879103664610393009789 83866454663874228897378671)
      ·
        refine ⟨125799681995811343346068007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83866454663874228897378671 125799681995811343346068007)
        ·
          refine ⟨188699522993717015019102011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125799681995811343346068007 188699522993717015019102011)
          ·
            refine ⟨283049284490575522528653017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188699522993717015019102011 283049284490575522528653017)
            ·
              refine ⟨212286963367931641896489763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283049284490575522528653017 212286963367931641896489763)
              ·
                refine ⟨318430445051897462844734645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212286963367931641896489763 318430445051897462844734645)
                ·
                  refine ⟨29852854223615387141693873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 318430445051897462844734645 29852854223615387141693873)
                  ·
                    refine ⟨22389640667711540356270405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29852854223615387141693873 22389640667711540356270405)
                    ·
                      refine ⟨4198057625195913816800701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22389640667711540356270405 4198057625195913816800701)
                      ·
                        rfl

theorem cell23_8175688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_8175688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175688 prefixEnd_8175688 := by exact prefixLift 8175688
  have htrace : WordTrace (prefixWord ++ tailWord_8175688) baseStart_8175688 baseEnd_8175688 := by
    simpa [prefixWord, tailWord_8175688, baseEnd_8175688] using wordTrace_append hprefix tailTrace_8175688
  have hstable : (prefixWord ++ tailWord_8175688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175688).length < 2 ^ (prefixWord ++ tailWord_8175688).sum := by decide
  have hdescent : baseEnd_8175688 < baseStart_8175688 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175709 : List Nat := [1, 4, 4, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_8175709 : Nat := 118140960795 + 8175709 * 2 ^ 59
def prefixEnd_8175709 : Nat := 4983230072969 + 3 ^ 40 * 8175709 * 2
def baseEnd_8175709 : Nat := 4198068408289658234638105

theorem tailTrace_8175709 : CollatzResearch.WordTrace tailWord_8175709 prefixEnd_8175709 4198068408289658234638105 := by
  unfold tailWord_8175709
  simp only [CollatzResearch.WordTrace]
  refine ⟨298192604737810067777194181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198795069825206711851462787 298192604737810067777194181)
  ·
    refine ⟨55911113388339387708223909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298192604737810067777194181 55911113388339387708223909)
    ·
      refine ⟨10483333760313635195291983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55911113388339387708223909 10483333760313635195291983)
      ·
        refine ⟨15725000640470452792937975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10483333760313635195291983 15725000640470452792937975)
        ·
          refine ⟨23587500960705679189406963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15725000640470452792937975 23587500960705679189406963)
          ·
            refine ⟨35381251441058518784110445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23587500960705679189406963 35381251441058518784110445)
            ·
              refine ⟨13267969290396944544041417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35381251441058518784110445 13267969290396944544041417)
              ·
                refine ⟨9950976967797708408031063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13267969290396944544041417 9950976967797708408031063)
                ·
                  refine ⟨14926465451696562612046595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9950976967797708408031063 14926465451696562612046595)
                  ·
                    refine ⟨22389698177544843918069893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14926465451696562612046595 22389698177544843918069893)
                    ·
                      refine ⟨4198068408289658234638105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22389698177544843918069893 4198068408289658234638105)
                      ·
                        rfl

theorem cell23_8175709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_8175709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175709 prefixEnd_8175709 := by exact prefixLift 8175709
  have htrace : WordTrace (prefixWord ++ tailWord_8175709) baseStart_8175709 baseEnd_8175709 := by
    simpa [prefixWord, tailWord_8175709, baseEnd_8175709] using wordTrace_append hprefix tailTrace_8175709
  have hstable : (prefixWord ++ tailWord_8175709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175709).length < 2 ^ (prefixWord ++ tailWord_8175709).sum := by decide
  have hdescent : baseEnd_8175709 < baseStart_8175709 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175712 : List Nat := [2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 3]
def baseStart_8175712 : Nat := 118140960795 + 8175712 * 2 ^ 59
def prefixEnd_8175712 : Nat := 4983230072969 + 3 ^ 40 * 8175712 * 2
def baseEnd_8175712 : Nat := 4198069948731621722900591

theorem tailTrace_8175712 : CollatzResearch.WordTrace tailWord_8175712 prefixEnd_8175712 4198069948731621722900591 := by
  unfold tailWord_8175712
  simp only [CollatzResearch.WordTrace]
  refine ⟨149096357078399599644776695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198795142771199466193035593 149096357078399599644776695)
  ·
    refine ⟨223644535617599399467165043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149096357078399599644776695 223644535617599399467165043)
    ·
      refine ⟨335466803426399099200747565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223644535617599399467165043 335466803426399099200747565)
      ·
        refine ⟨125800051284899662200280337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335466803426399099200747565 125800051284899662200280337)
        ·
          refine ⟨94350038463674746650210253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125800051284899662200280337 94350038463674746650210253)
          ·
            refine ⟨35381264423878029993828845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94350038463674746650210253 35381264423878029993828845)
            ·
              refine ⟨13267974158954261247685817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35381264423878029993828845 13267974158954261247685817)
              ·
                refine ⟨9950980619215695935764363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13267974158954261247685817 9950980619215695935764363)
                ·
                  refine ⟨14926470928823543903646545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9950980619215695935764363 14926470928823543903646545)
                  ·
                    refine ⟨11194853196617657927734909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14926470928823543903646545 11194853196617657927734909)
                    ·
                      refine ⟨4198069948731621722900591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11194853196617657927734909 4198069948731621722900591)
                      ·
                        rfl

theorem cell23_8175712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_8175712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175712 prefixEnd_8175712 := by exact prefixLift 8175712
  have htrace : WordTrace (prefixWord ++ tailWord_8175712) baseStart_8175712 baseEnd_8175712 := by
    simpa [prefixWord, tailWord_8175712, baseEnd_8175712] using wordTrace_append hprefix tailTrace_8175712
  have hstable : (prefixWord ++ tailWord_8175712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175712).length < 2 ^ (prefixWord ++ tailWord_8175712).sum := by decide
  have hdescent : baseEnd_8175712 < baseStart_8175712 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175722 : List Nat := [3, 1, 3, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_8175722 : Nat := 118140960795 + 8175722 * 2 ^ 59
def prefixEnd_8175722 : Nat := 4983230072969 + 3 ^ 40 * 8175722 * 2
def baseEnd_8175722 : Nat := 4198075083538166683775545

theorem tailTrace_8175722 : CollatzResearch.WordTrace tailWord_8175722 prefixEnd_8175722 4198075083538166683775545 := by
  unfold tailWord_8175722
  simp only [CollatzResearch.WordTrace]
  refine ⟨74548269721690742749354355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198795385924508647331611613 74548269721690742749354355)
  ·
    refine ⟨111822404582536114124031533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74548269721690742749354355 111822404582536114124031533)
    ·
      refine ⟨41933401718451042796511825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111822404582536114124031533 41933401718451042796511825)
      ·
        refine ⟨31450051288838282097383869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41933401718451042796511825 31450051288838282097383869)
        ·
          refine ⟨11793769233314355786518951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31450051288838282097383869 11793769233314355786518951)
          ·
            refine ⟨17690653849971533679778427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11793769233314355786518951 17690653849971533679778427)
            ·
              refine ⟨26535980774957300519667641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17690653849971533679778427 26535980774957300519667641)
              ·
                refine ⟨19901985581217975389750731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26535980774957300519667641 19901985581217975389750731)
                ·
                  refine ⟨29852978371826963084626097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19901985581217975389750731 29852978371826963084626097)
                  ·
                    refine ⟨22389733778870222313469573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29852978371826963084626097 22389733778870222313469573)
                    ·
                      refine ⟨4198075083538166683775545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22389733778870222313469573 4198075083538166683775545)
                      ·
                        rfl

theorem cell23_8175722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_8175722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175722 prefixEnd_8175722 := by exact prefixLift 8175722
  have htrace : WordTrace (prefixWord ++ tailWord_8175722) baseStart_8175722 baseEnd_8175722 := by
    simpa [prefixWord, tailWord_8175722, baseEnd_8175722] using wordTrace_append hprefix tailTrace_8175722
  have hstable : (prefixWord ++ tailWord_8175722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175722).length < 2 ^ (prefixWord ++ tailWord_8175722).sum := by decide
  have hdescent : baseEnd_8175722 < baseStart_8175722 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175726 : List Nat := [4, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2]
def baseStart_8175726 : Nat := 118140960795 + 8175726 * 2 ^ 59
def prefixEnd_8175726 : Nat := 4983230072969 + 3 ^ 40 * 8175726 * 2
def baseEnd_8175726 : Nat := 4198077137460784668125527

theorem tailTrace_8175726 : CollatzResearch.WordTrace tailWord_8175726 prefixEnd_8175726 4198077137460784668125527 := by
  unfold tailWord_8175726
  simp only [CollatzResearch.WordTrace]
  refine ⟨37274153097343559960070379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198795483185832319787042021 37274153097343559960070379)
  ·
    refine ⟨55911229646015339940105569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37274153097343559960070379 55911229646015339940105569)
    ·
      refine ⟨41933422234511504955079177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55911229646015339940105569 41933422234511504955079177)
      ·
        refine ⟨31450066675883628716309383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41933422234511504955079177 31450066675883628716309383)
        ·
          refine ⟨47175100013825443074464075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31450066675883628716309383 47175100013825443074464075)
          ·
            refine ⟨70762650020738164611696113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47175100013825443074464075 70762650020738164611696113)
            ·
              refine ⟨53071987515553623458772085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70762650020738164611696113 53071987515553623458772085)
              ·
                refine ⟨4975498829583152199259883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53071987515553623458772085 4975498829583152199259883)
                ·
                  refine ⟨7463248244374728298889825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4975498829583152199259883 7463248244374728298889825)
                  ·
                    refine ⟨5597436183281046224167369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7463248244374728298889825 5597436183281046224167369)
                    ·
                      refine ⟨4198077137460784668125527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5597436183281046224167369 4198077137460784668125527)
                      ·
                        rfl

theorem cell23_8175726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_8175726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175726 prefixEnd_8175726 := by exact prefixLift 8175726
  have htrace : WordTrace (prefixWord ++ tailWord_8175726) baseStart_8175726 baseEnd_8175726 := by
    simpa [prefixWord, tailWord_8175726, baseEnd_8175726] using wordTrace_append hprefix tailTrace_8175726
  have hstable : (prefixWord ++ tailWord_8175726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175726).length < 2 ^ (prefixWord ++ tailWord_8175726).sum := by decide
  have hdescent : baseEnd_8175726 < baseStart_8175726 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175793 : List Nat := [1, 2, 2, 5, 3, 1, 1, 2, 2, 1, 3]
def baseStart_8175793 : Nat := 118140960795 + 8175793 * 2 ^ 59
def prefixEnd_8175793 : Nat := 4983230072969 + 3 ^ 40 * 8175793 * 2
def baseEnd_8175793 : Nat := 4198111540664635905987719

theorem tailTrace_8175793 : CollatzResearch.WordTrace tailWord_8175793 prefixEnd_8175793 4198111540664635905987719 := by
  unfold tailWord_8175793
  simp only [CollatzResearch.WordTrace]
  refine ⟨298195668469505750123252033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198797112313003833415501355 298195668469505750123252033)
  ·
    refine ⟨223646751352129312592439025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298195668469505750123252033 223646751352129312592439025)
    ·
      refine ⟨167735063514096984444329269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223646751352129312592439025 167735063514096984444329269)
      ·
        refine ⟨15725162204446592291655869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167735063514096984444329269 15725162204446592291655869)
        ·
          refine ⟨5896935826667472109370951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15725162204446592291655869 5896935826667472109370951)
          ·
            refine ⟨8845403740001208164056427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5896935826667472109370951 8845403740001208164056427)
            ·
              refine ⟨13268105610001812246084641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8845403740001208164056427 13268105610001812246084641)
              ·
                refine ⟨9951079207501359184563481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13268105610001812246084641 9951079207501359184563481)
                ·
                  refine ⟨7463309405626019388422611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9951079207501359184563481 7463309405626019388422611)
                  ·
                    refine ⟨11194964108439029082633917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7463309405626019388422611 11194964108439029082633917)
                    ·
                      refine ⟨4198111540664635905987719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11194964108439029082633917 4198111540664635905987719)
                      ·
                        rfl

theorem cell23_8175793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_8175793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175793 prefixEnd_8175793 := by exact prefixLift 8175793
  have htrace : WordTrace (prefixWord ++ tailWord_8175793) baseStart_8175793 baseEnd_8175793 := by
    simpa [prefixWord, tailWord_8175793, baseEnd_8175793] using wordTrace_append hprefix tailTrace_8175793
  have hstable : (prefixWord ++ tailWord_8175793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175793).length < 2 ^ (prefixWord ++ tailWord_8175793).sum := by decide
  have hdescent : baseEnd_8175793 < baseStart_8175793 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175799 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 4, 2, 2]
def baseStart_8175799 : Nat := 118140960795 + 8175799 * 2 ^ 59
def prefixEnd_8175799 : Nat := 4983230072969 + 3 ^ 40 * 8175799 * 2
def baseEnd_8175799 : Nat := 4198114621548562882512691

theorem tailTrace_8175799 : CollatzResearch.WordTrace tailWord_8175799 prefixEnd_8175799 4198114621548562882512691 := by
  unfold tailWord_8175799
  simp only [CollatzResearch.WordTrace]
  refine ⟨298195887307484013147970451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198797258204989342098646967 298195887307484013147970451)
  ·
    refine ⟨447293830961226019721955677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298195887307484013147970451 447293830961226019721955677)
    ·
      refine ⟨167735186610459757395733379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447293830961226019721955677 167735186610459757395733379)
      ·
        refine ⟨251602779915689636093600069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167735186610459757395733379 251602779915689636093600069)
        ·
          refine ⟨47175521234191806767550013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251602779915689636093600069 47175521234191806767550013)
          ·
            refine ⟨17690820462821927537831255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47175521234191806767550013 17690820462821927537831255)
            ·
              refine ⟨26536230694232891306746883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17690820462821927537831255 26536230694232891306746883)
              ·
                refine ⟨39804346041349336960120325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26536230694232891306746883 39804346041349336960120325)
                ·
                  refine ⟨7463314882753000680022561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39804346041349336960120325 7463314882753000680022561)
                  ·
                    refine ⟨5597486162064750510016921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7463314882753000680022561 5597486162064750510016921)
                    ·
                      refine ⟨4198114621548562882512691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5597486162064750510016921 4198114621548562882512691)
                      ·
                        rfl

theorem cell23_8175799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 2, 2].length) (baseStart_8175799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175799 prefixEnd_8175799 := by exact prefixLift 8175799
  have htrace : WordTrace (prefixWord ++ tailWord_8175799) baseStart_8175799 baseEnd_8175799 := by
    simpa [prefixWord, tailWord_8175799, baseEnd_8175799] using wordTrace_append hprefix tailTrace_8175799
  have hstable : (prefixWord ++ tailWord_8175799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175799).length < 2 ^ (prefixWord ++ tailWord_8175799).sum := by decide
  have hdescent : baseEnd_8175799 < baseStart_8175799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175810 : List Nat := [3, 5, 1, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_8175810 : Nat := 118140960795 + 8175810 * 2 ^ 59
def prefixEnd_8175810 : Nat := 4983230072969 + 3 ^ 40 * 8175810 * 2
def baseEnd_8175810 : Nat := 4198120269835762339475141

theorem tailTrace_8175810 : CollatzResearch.WordTrace tailWord_8175810 prefixEnd_8175810 4198120269835762339475141 := by
  unfold tailWord_8175810
  simp only [CollatzResearch.WordTrace]
  refine ⟨74549072127611040506655221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198797525673629441351080589 74549072127611040506655221)
  ·
    refine ⟨6988975511963535047498927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74549072127611040506655221 6988975511963535047498927)
    ·
      refine ⟨10483463267945302571248391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6988975511963535047498927 10483463267945302571248391)
      ·
        refine ⟨15725194901917953856872587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10483463267945302571248391 15725194901917953856872587)
        ·
          refine ⟨23587792352876930785308881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15725194901917953856872587 23587792352876930785308881)
          ·
            refine ⟨17690844264657698088981661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23587792352876930785308881 17690844264657698088981661)
            ·
              refine ⟨6634066599246636783368123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17690844264657698088981661 6634066599246636783368123)
              ·
                refine ⟨9951099898869955175052185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6634066599246636783368123 9951099898869955175052185)
                ·
                  refine ⟨7463324924152466381289139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9951099898869955175052185 7463324924152466381289139)
                  ·
                    refine ⟨11194987386228699571933709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7463324924152466381289139 11194987386228699571933709)
                    ·
                      refine ⟨4198120269835762339475141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11194987386228699571933709 4198120269835762339475141)
                      ·
                        rfl

theorem cell23_8175810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_8175810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175810 prefixEnd_8175810 := by exact prefixLift 8175810
  have htrace : WordTrace (prefixWord ++ tailWord_8175810) baseStart_8175810 baseEnd_8175810 := by
    simpa [prefixWord, tailWord_8175810, baseEnd_8175810] using wordTrace_append hprefix tailTrace_8175810
  have hstable : (prefixWord ++ tailWord_8175810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175810).length < 2 ^ (prefixWord ++ tailWord_8175810).sum := by decide
  have hdescent : baseEnd_8175810 < baseStart_8175810 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175812 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_8175812 : Nat := 118140960795 + 8175812 * 2 ^ 59
def prefixEnd_8175812 : Nat := 4983230072969 + 3 ^ 40 * 8175812 * 2
def baseEnd_8175812 : Nat := 4198121296797071331650131

theorem tailTrace_8175812 : CollatzResearch.WordTrace tailWord_8175812 prefixEnd_8175812 4198121296797071331650131 := by
  unfold tailWord_8175812
  simp only [CollatzResearch.WordTrace]
  refine ⟨149098180728218458184096845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198797574304291277578795793 149098180728218458184096845)
  ·
    refine ⟨55911817773081921819036317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149098180728218458184096845 55911817773081921819036317)
    ·
      refine ⟨20966931664905720682138619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55911817773081921819036317 20966931664905720682138619)
      ·
        refine ⟨31450397497358581023207929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20966931664905720682138619 31450397497358581023207929)
        ·
          refine ⟨23587798123018935767405947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31450397497358581023207929 23587798123018935767405947)
          ·
            refine ⟨35381697184528403651108921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23587798123018935767405947 35381697184528403651108921)
            ·
              refine ⟨26536272888396302738331691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35381697184528403651108921 26536272888396302738331691)
              ·
                refine ⟨39804409332594454107497537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26536272888396302738331691 39804409332594454107497537)
                ·
                  refine ⟨29853306999445840580623153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39804409332594454107497537 29853306999445840580623153)
                  ·
                    refine ⟨22389980249584380435467365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29853306999445840580623153 22389980249584380435467365)
                    ·
                      refine ⟨4198121296797071331650131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22389980249584380435467365 4198121296797071331650131)
                      ·
                        rfl

theorem cell23_8175812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_8175812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175812 prefixEnd_8175812 := by exact prefixLift 8175812
  have htrace : WordTrace (prefixWord ++ tailWord_8175812) baseStart_8175812 baseEnd_8175812 := by
    simpa [prefixWord, tailWord_8175812, baseEnd_8175812] using wordTrace_append hprefix tailTrace_8175812
  have hstable : (prefixWord ++ tailWord_8175812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175812).length < 2 ^ (prefixWord ++ tailWord_8175812).sum := by decide
  have hdescent : baseEnd_8175812 < baseStart_8175812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175872 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 2, 4, 2]
def baseStart_8175872 : Nat := 118140960795 + 8175872 * 2 ^ 59
def prefixEnd_8175872 : Nat := 4983230072969 + 3 ^ 40 * 8175872 * 2
def baseEnd_8175872 : Nat := 4198152105636341096899855

theorem tailTrace_8175872 : CollatzResearch.WordTrace tailWord_8175872 prefixEnd_8175872 4198152105636341096899855 := by
  unfold tailWord_8175872
  simp only [CollatzResearch.WordTrace]
  refine ⟨149099274918109773307688935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198799033224146364410251913 149099274918109773307688935)
  ·
    refine ⟨223648912377164659961533403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149099274918109773307688935 223648912377164659961533403)
    ·
      refine ⟨335473368565746989942300105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223648912377164659961533403 335473368565746989942300105)
      ·
        refine ⟨251605026424310242456725079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335473368565746989942300105 251605026424310242456725079)
        ·
          refine ⟨377407539636465363685087619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251605026424310242456725079 377407539636465363685087619)
          ·
            refine ⟨566111309454698045527631429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377407539636465363685087619 566111309454698045527631429)
            ·
              refine ⟨106145870522755883536430893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 566111309454698045527631429 106145870522755883536430893)
              ·
                refine ⟨39804701446033456326161585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106145870522755883536430893 39804701446033456326161585)
                ·
                  refine ⟨29853526084525092244621189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39804701446033456326161585 29853526084525092244621189)
                  ·
                    refine ⟨5597536140848454795866473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29853526084525092244621189 5597536140848454795866473)
                    ·
                      refine ⟨4198152105636341096899855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5597536140848454795866473 4198152105636341096899855)
                      ·
                        rfl

theorem cell23_8175872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 4, 2].length) (baseStart_8175872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175872 prefixEnd_8175872 := by exact prefixLift 8175872
  have htrace : WordTrace (prefixWord ++ tailWord_8175872) baseStart_8175872 baseEnd_8175872 := by
    simpa [prefixWord, tailWord_8175872, baseEnd_8175872] using wordTrace_append hprefix tailTrace_8175872
  have hstable : (prefixWord ++ tailWord_8175872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175872).length < 2 ^ (prefixWord ++ tailWord_8175872).sum := by decide
  have hdescent : baseEnd_8175872 < baseStart_8175872 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175882 : List Nat := [3, 1, 2, 2, 1, 1, 2, 4, 3, 4]
def baseStart_8175882 : Nat := 118140960795 + 8175882 * 2 ^ 59
def prefixEnd_8175882 : Nat := 4983230072969 + 3 ^ 40 * 8175882 * 2
def baseEnd_8175882 : Nat := 1399385746814295352591603

theorem tailTrace_8175882 : CollatzResearch.WordTrace tailWord_8175882 prefixEnd_8175882 1399385746814295352591603 := by
  unfold tailWord_8175882
  simp only [CollatzResearch.WordTrace]
  refine ⟨74549728641545829580810475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198799276377455545548827933 74549728641545829580810475)
  ·
    refine ⟨111824592962318744371215713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74549728641545829580810475 111824592962318744371215713)
    ·
      refine ⟨83868444721739058278411785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111824592962318744371215713 83868444721739058278411785)
      ·
        refine ⟨62901333541304293708808839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83868444721739058278411785 62901333541304293708808839)
        ·
          refine ⟨94352000311956440563213259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62901333541304293708808839 94352000311956440563213259)
          ·
            refine ⟨141528000467934660844819889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94352000311956440563213259 141528000467934660844819889)
            ·
              refine ⟨106146000350950995633614917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141528000467934660844819889 106146000350950995633614917)
              ·
                refine ⟨19902375065803311681302797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106146000350950995633614917 19902375065803311681302797)
                ·
                  refine ⟨7463390649676241880488549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19902375065803311681302797 7463390649676241880488549)
                  ·
                    refine ⟨1399385746814295352591603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7463390649676241880488549 1399385746814295352591603)
                    ·
                      rfl

theorem cell23_8175882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_8175882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175882 prefixEnd_8175882 := by exact prefixLift 8175882
  have htrace : WordTrace (prefixWord ++ tailWord_8175882) baseStart_8175882 baseEnd_8175882 := by
    simpa [prefixWord, tailWord_8175882, baseEnd_8175882] using wordTrace_append hprefix tailTrace_8175882
  have hstable : (prefixWord ++ tailWord_8175882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175882).length < 2 ^ (prefixWord ++ tailWord_8175882).sum := by decide
  have hdescent : baseEnd_8175882 < baseStart_8175882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175916 : List Nat := [2, 2, 1, 1, 1, 3, 6, 2, 1, 4]
def baseStart_8175916 : Nat := 118140960795 + 8175916 * 2 ^ 59
def prefixEnd_8175916 : Nat := 4983230072969 + 3 ^ 40 * 8175916 * 2
def baseEnd_8175916 : Nat := 1399391566261712974916551

theorem tailTrace_8175916 : CollatzResearch.WordTrace tailWord_8175916 prefixEnd_8175916 1399391566261712974916551 := by
  unfold tailWord_8175916
  simp only [CollatzResearch.WordTrace]
  refine ⟨149100077324030071064989801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198800103098706761419986401 149100077324030071064989801)
  ·
    refine ⟨111825057993022553298742351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149100077324030071064989801 111825057993022553298742351)
    ·
      refine ⟨167737586989533829948113527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111825057993022553298742351 167737586989533829948113527)
      ·
        refine ⟨251606380484300744922170291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167737586989533829948113527 251606380484300744922170291)
        ·
          refine ⟨377409570726451117383255437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251606380484300744922170291 377409570726451117383255437)
          ·
            refine ⟨141528589022419169018720789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377409570726451117383255437 141528589022419169018720789)
            ·
              refine ⟨6634152610425898547752537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141528589022419169018720789 6634152610425898547752537)
              ·
                refine ⟨4975614457819423910814403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6634152610425898547752537 4975614457819423910814403)
                ·
                  refine ⟨7463421686729135866221605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4975614457819423910814403 7463421686729135866221605)
                  ·
                    refine ⟨1399391566261712974916551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7463421686729135866221605 1399391566261712974916551)
                    ·
                      rfl

theorem cell23_8175916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 1, 4].length) (baseStart_8175916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175916 prefixEnd_8175916 := by exact prefixLift 8175916
  have htrace : WordTrace (prefixWord ++ tailWord_8175916) baseStart_8175916 baseEnd_8175916 := by
    simpa [prefixWord, tailWord_8175916, baseEnd_8175916] using wordTrace_append hprefix tailTrace_8175916
  have hstable : (prefixWord ++ tailWord_8175916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175916).length < 2 ^ (prefixWord ++ tailWord_8175916).sum := by decide
  have hdescent : baseEnd_8175916 < baseStart_8175916 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175935 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 7]
def baseStart_8175935 : Nat := 118140960795 + 8175935 * 2 ^ 59
def prefixEnd_8175935 : Nat := 4983230072969 + 3 ^ 40 * 8175935 * 2
def baseEnd_8175935 : Nat := 4198184454917574350412065

theorem tailTrace_8175935 : CollatzResearch.WordTrace tailWord_8175935 prefixEnd_8175935 4198184454917574350412065 := by
  unfold tailWord_8175935
  simp only [CollatzResearch.WordTrace]
  refine ⟨298200847634991308374921259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198800565089994205583280839 298200847634991308374921259)
  ·
    refine ⟨447301271452486962562381889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298200847634991308374921259 447301271452486962562381889)
    ·
      refine ⟨335475953589365221921786417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447301271452486962562381889 335475953589365221921786417)
      ·
        refine ⟨251606965192023916441339813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335475953589365221921786417 251606965192023916441339813)
        ·
          refine ⟨47176305973504484332751215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251606965192023916441339813 47176305973504484332751215)
          ·
            refine ⟨70764458960256726499126823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47176305973504484332751215 70764458960256726499126823)
            ·
              refine ⟨106146688440385089748690235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70764458960256726499126823 106146688440385089748690235)
              ·
                refine ⟨159220032660577634623035353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106146688440385089748690235 159220032660577634623035353)
                ·
                  refine ⟨119415024495433225967276515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159220032660577634623035353 119415024495433225967276515)
                  ·
                    refine ⟨179122536743149838950914773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119415024495433225967276515 179122536743149838950914773)
                    ·
                      refine ⟨4198184454917574350412065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179122536743149838950914773 4198184454917574350412065)
                      ·
                        rfl

theorem cell23_8175935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_8175935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175935 prefixEnd_8175935 := by exact prefixLift 8175935
  have htrace : WordTrace (prefixWord ++ tailWord_8175935) baseStart_8175935 baseEnd_8175935 := by
    simpa [prefixWord, tailWord_8175935, baseEnd_8175935] using wordTrace_append hprefix tailTrace_8175935
  have hstable : (prefixWord ++ tailWord_8175935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175935).length < 2 ^ (prefixWord ++ tailWord_8175935).sum := by decide
  have hdescent : baseEnd_8175935 < baseStart_8175935 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175955 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 3, 6]
def baseStart_8175955 : Nat := 118140960795 + 8175955 * 2 ^ 59
def prefixEnd_8175955 : Nat := 4983230072969 + 3 ^ 40 * 8175955 * 2
def baseEnd_8175955 : Nat := 1399398241510221424053991

theorem tailTrace_8175955 : CollatzResearch.WordTrace tailWord_8175955 prefixEnd_8175955 1399398241510221424053991 := by
  unfold tailWord_8175955
  simp only [CollatzResearch.WordTrace]
  refine ⟨298201577094918851790649319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198801051396612567860432879 298201577094918851790649319)
  ·
    refine ⟨447302365642378277685973979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298201577094918851790649319 447302365642378277685973979)
    ·
      refine ⟨670953548463567416528960969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447302365642378277685973979 670953548463567416528960969)
      ·
        refine ⟨503215161347675562396720727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670953548463567416528960969 503215161347675562396720727)
        ·
          refine ⟨754822742021513343595081091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503215161347675562396720727 754822742021513343595081091)
          ·
            refine ⟨1132234113032270015392621637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754822742021513343595081091 1132234113032270015392621637)
            ·
              refine ⟨212293896193550627886116557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1132234113032270015392621637 212293896193550627886116557)
              ·
                refine ⟨79610211072581485457293709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212293896193550627886116557 79610211072581485457293709)
                ·
                  refine ⟨29853829152218057046485141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79610211072581485457293709 29853829152218057046485141)
                  ·
                    refine ⟨1399398241510221424053991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29853829152218057046485141 1399398241510221424053991)
                    ·
                      rfl

theorem cell23_8175955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 6].length) (baseStart_8175955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175955 prefixEnd_8175955 := by exact prefixLift 8175955
  have htrace : WordTrace (prefixWord ++ tailWord_8175955) baseStart_8175955 baseEnd_8175955 := by
    simpa [prefixWord, tailWord_8175955, baseEnd_8175955] using wordTrace_append hprefix tailTrace_8175955
  have hstable : (prefixWord ++ tailWord_8175955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175955).length < 2 ^ (prefixWord ++ tailWord_8175955).sum := by decide
  have hdescent : baseEnd_8175955 < baseStart_8175955 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175979 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 7, 2, 2]
def baseStart_8175979 : Nat := 118140960795 + 8175979 * 2 ^ 59
def prefixEnd_8175979 : Nat := 4983230072969 + 3 ^ 40 * 8175979 * 2
def baseEnd_8175979 : Nat := 4198207048066372178261863

theorem tailTrace_8175979 : CollatzResearch.WordTrace tailWord_8175979 prefixEnd_8175979 4198207048066372178261863 := by
  unfold tailWord_8175979
  simp only [CollatzResearch.WordTrace]
  refine ⟨298202452446831903889522991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198801634964554602593015327 298202452446831903889522991)
  ·
    refine ⟨447303678670247855834284487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298202452446831903889522991 447303678670247855834284487)
    ·
      refine ⟨670955518005371783751426731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447303678670247855834284487 670955518005371783751426731)
      ·
        refine ⟨1006433277008057675627140097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670955518005371783751426731 1006433277008057675627140097)
        ·
          refine ⟨754824957756043256720355073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1006433277008057675627140097 754824957756043256720355073)
          ·
            refine ⟨566118718317032442540266305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 754824957756043256720355073 566118718317032442540266305)
            ·
              refine ⟨424589038737774331905199729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 566118718317032442540266305 424589038737774331905199729)
              ·
                refine ⟨318441779053330748928899797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424589038737774331905199729 318441779053330748928899797)
                ·
                  refine ⟨7463479196562439428021089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 318441779053330748928899797 7463479196562439428021089)
                  ·
                    refine ⟨5597609397421829571015817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7463479196562439428021089 5597609397421829571015817)
                    ·
                      refine ⟨4198207048066372178261863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5597609397421829571015817 4198207048066372178261863)
                      ·
                        rfl

theorem cell23_8175979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 2, 2].length) (baseStart_8175979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175979 prefixEnd_8175979 := by exact prefixLift 8175979
  have htrace : WordTrace (prefixWord ++ tailWord_8175979) baseStart_8175979 baseEnd_8175979 := by
    simpa [prefixWord, tailWord_8175979, baseEnd_8175979] using wordTrace_append hprefix tailTrace_8175979
  have hstable : (prefixWord ++ tailWord_8175979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175979).length < 2 ^ (prefixWord ++ tailWord_8175979).sum := by decide
  have hdescent : baseEnd_8175979 < baseStart_8175979 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175985 : List Nat := [1, 2, 2, 2, 1, 2, 1, 12]
def baseStart_8175985 : Nat := 118140960795 + 8175985 * 2 ^ 59
def prefixEnd_8175985 : Nat := 4983230072969 + 3 ^ 40 * 8175985 * 2
def baseEnd_8175985 : Nat := 155489264035196264992105

theorem tailTrace_8175985 : CollatzResearch.WordTrace tailWord_8175985 prefixEnd_8175985 155489264035196264992105 := by
  unfold tailWord_8175985
  simp only [CollatzResearch.WordTrace]
  refine ⟨298202671284810166914241409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198801780856540111276160939 298202671284810166914241409)
  ·
    refine ⟨223652003463607625185681057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298202671284810166914241409 223652003463607625185681057)
    ·
      refine ⟨167739002597705718889260793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223652003463607625185681057 167739002597705718889260793)
      ·
        refine ⟨125804251948279289166945595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167739002597705718889260793 125804251948279289166945595)
        ·
          refine ⟨188706377922418933750418393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125804251948279289166945595 188706377922418933750418393)
          ·
            refine ⟨141529783441814200312813795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188706377922418933750418393 141529783441814200312813795)
            ·
              refine ⟨212294675162721300469220693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141529783441814200312813795 212294675162721300469220693)
              ·
                refine ⟨155489264035196264992105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 212294675162721300469220693 155489264035196264992105)
                ·
                  rfl

theorem cell23_8175985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 12].length) (baseStart_8175985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175985 prefixEnd_8175985 := by exact prefixLift 8175985
  have htrace : WordTrace (prefixWord ++ tailWord_8175985) baseStart_8175985 baseEnd_8175985 := by
    simpa [prefixWord, tailWord_8175985, baseEnd_8175985] using wordTrace_append hprefix tailTrace_8175985
  have hstable : (prefixWord ++ tailWord_8175985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175985).length < 2 ^ (prefixWord ++ tailWord_8175985).sum := by decide
  have hdescent : baseEnd_8175985 < baseStart_8175985 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8175989 : List Nat := [1, 3, 4, 1, 2, 1, 3, 1, 1, 6]
def baseStart_8175989 : Nat := 118140960795 + 8175989 * 2 ^ 59
def prefixEnd_8175989 : Nat := 4983230072969 + 3 ^ 40 * 8175989 * 2
def baseEnd_8175989 : Nat := 1399404060957639046378939

theorem tailTrace_8175989 : CollatzResearch.WordTrace tailWord_8175989 prefixEnd_8175989 1399404060957639046378939 := by
  unfold tailWord_8175989
  simp only [CollatzResearch.WordTrace]
  refine ⟨298202817176795675597387021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198801878117863783731591347 298202817176795675597387021)
  ·
    refine ⟨111826056441298378349020133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298202817176795675597387021 111826056441298378349020133)
    ·
      refine ⟨20967385582743445940441275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111826056441298378349020133 20967385582743445940441275)
      ·
        refine ⟨31451078374115168910661913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20967385582743445940441275 31451078374115168910661913)
        ·
          refine ⟨23588308780586376682996435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31451078374115168910661913 23588308780586376682996435)
          ·
            refine ⟨35382463170879565024494653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23588308780586376682996435 35382463170879565024494653)
            ·
              refine ⟨13268423689079836884185495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35382463170879565024494653 13268423689079836884185495)
              ·
                refine ⟨19902635533619755326278243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13268423689079836884185495 19902635533619755326278243)
                ·
                  refine ⟨29853953300429632989417365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19902635533619755326278243 29853953300429632989417365)
                  ·
                    refine ⟨1399404060957639046378939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29853953300429632989417365 1399404060957639046378939)
                    ·
                      rfl

theorem cell23_8175989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_8175989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8175989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8175989 prefixEnd_8175989 := by exact prefixLift 8175989
  have htrace : WordTrace (prefixWord ++ tailWord_8175989) baseStart_8175989 baseEnd_8175989 := by
    simpa [prefixWord, tailWord_8175989, baseEnd_8175989] using wordTrace_append hprefix tailTrace_8175989
  have hstable : (prefixWord ++ tailWord_8175989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8175989).length < 2 ^ (prefixWord ++ tailWord_8175989).sum := by decide
  have hdescent : baseEnd_8175989 < baseStart_8175989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8175989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176030 : List Nat := [4, 3, 1, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_8176030 : Nat := 118140960795 + 8176030 * 2 ^ 59
def prefixEnd_8176030 : Nat := 4983230072969 + 3 ^ 40 * 8176030 * 2
def baseEnd_8176030 : Nat := 4198233235579751478724129

theorem tailTrace_8176030 : CollatzResearch.WordTrace tailWord_8176030 prefixEnd_8176030 4198233235579751478724129 := by
  unfold tailWord_8176030
  simp only [CollatzResearch.WordTrace]
  refine ⟨37275539071205892449953693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198802875046431426399753029 37275539071205892449953693)
  ·
    refine ⟨13978327151702209668732635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37275539071205892449953693 13978327151702209668732635)
    ·
      refine ⟨20967490727553314503098953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13978327151702209668732635 20967490727553314503098953)
      ·
        refine ⟨15725618045664985877324215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20967490727553314503098953 15725618045664985877324215)
        ·
          refine ⟨23588427068497478815986323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15725618045664985877324215 23588427068497478815986323)
          ·
            refine ⟨35382640602746218223979485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23588427068497478815986323 35382640602746218223979485)
            ·
              refine ⟨13268490226029831833992307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35382640602746218223979485 13268490226029831833992307)
              ·
                refine ⟨19902735339044747750988461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13268490226029831833992307 19902735339044747750988461)
                ·
                  refine ⟨7463525752141780406620673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19902735339044747750988461 7463525752141780406620673)
                  ·
                    refine ⟨5597644314106335304965505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7463525752141780406620673 5597644314106335304965505)
                    ·
                      refine ⟨4198233235579751478724129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5597644314106335304965505 4198233235579751478724129)
                      ·
                        rfl

theorem cell23_8176030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_8176030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176030 prefixEnd_8176030 := by exact prefixLift 8176030
  have htrace : WordTrace (prefixWord ++ tailWord_8176030) baseStart_8176030 baseEnd_8176030 := by
    simpa [prefixWord, tailWord_8176030, baseEnd_8176030] using wordTrace_append hprefix tailTrace_8176030
  have hstable : (prefixWord ++ tailWord_8176030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176030).length < 2 ^ (prefixWord ++ tailWord_8176030).sum := by decide
  have hdescent : baseEnd_8176030 < baseStart_8176030 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176040 : List Nat := [2, 1, 6, 1, 1, 3, 2, 1, 2, 4]
def baseStart_8176040 : Nat := 118140960795 + 8176040 * 2 ^ 59
def prefixEnd_8176040 : Nat := 4983230072969 + 3 ^ 40 * 8176040 * 2
def baseEnd_8176040 : Nat := 1399412790128765479866361

theorem tailTrace_8176040 : CollatzResearch.WordTrace tailWord_8176040 prefixEnd_8176040 1399412790128765479866361 := by
  unfold tailWord_8176040
  simp only [CollatzResearch.WordTrace]
  refine ⟨149102338649805455653746787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198803118199740607538329049 149102338649805455653746787)
  ·
    refine ⟨223653507974708183480620181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149102338649805455653746787 223653507974708183480620181)
    ·
      refine ⟨10483758186314446100654071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 223653507974708183480620181 10483758186314446100654071)
      ·
        refine ⟨15725637279471669150981107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10483758186314446100654071 15725637279471669150981107)
        ·
          refine ⟨23588455919207503726471661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15725637279471669150981107 23588455919207503726471661)
          ·
            refine ⟨8845670969702813897426873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23588455919207503726471661 8845670969702813897426873)
            ·
              refine ⟨6634253227277110423070155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8845670969702813897426873 6634253227277110423070155)
              ·
                refine ⟨9951379840915665634605233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6634253227277110423070155 9951379840915665634605233)
                ·
                  refine ⟨7463534880686749225953925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9951379840915665634605233 7463534880686749225953925)
                  ·
                    refine ⟨1399412790128765479866361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7463534880686749225953925 1399412790128765479866361)
                    ·
                      rfl

theorem cell23_8176040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_8176040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176040 prefixEnd_8176040 := by exact prefixLift 8176040
  have htrace : WordTrace (prefixWord ++ tailWord_8176040) baseStart_8176040 baseEnd_8176040 := by
    simpa [prefixWord, tailWord_8176040, baseEnd_8176040] using wordTrace_append hprefix tailTrace_8176040
  have hstable : (prefixWord ++ tailWord_8176040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176040).length < 2 ^ (prefixWord ++ tailWord_8176040).sum := by decide
  have hdescent : baseEnd_8176040 < baseStart_8176040 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176103 : List Nat := [1, 1, 5, 2, 1, 1, 1, 5, 2, 2, 2]
def baseStart_8176103 : Nat := 118140960795 + 8176103 * 2 ^ 59
def prefixEnd_8176103 : Nat := 4983230072969 + 3 ^ 40 * 8176103 * 2
def baseEnd_8176103 : Nat := 4198270719667529693111293

theorem tailTrace_8176103 : CollatzResearch.WordTrace tailWord_8176103 prefixEnd_8176103 4198270719667529693111293 := by
  unfold tailWord_8176103
  simp only [CollatzResearch.WordTrace]
  refine ⟨298206975098382673067036963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198804650065588448711357975 298206975098382673067036963)
  ·
    refine ⟨447310462647574009600555445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298206975098382673067036963 447310462647574009600555445)
    ·
      refine ⟨41935355873210063400052073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 447310462647574009600555445 41935355873210063400052073)
      ·
        refine ⟨31451516904907547550039055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41935355873210063400052073 31451516904907547550039055)
        ·
          refine ⟨47177275357361321325058583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31451516904907547550039055 47177275357361321325058583)
          ·
            refine ⟨70765913036041981987587875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47177275357361321325058583 70765913036041981987587875)
            ·
              refine ⟨106148869554062972981381813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70765913036041981987587875 106148869554062972981381813)
              ·
                refine ⟨9951456520693403717004545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106148869554062972981381813 9951456520693403717004545)
                ·
                  refine ⟨7463592390520052787753409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9951456520693403717004545 7463592390520052787753409)
                  ·
                    refine ⟨5597694292890039590815057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7463592390520052787753409 5597694292890039590815057)
                    ·
                      refine ⟨4198270719667529693111293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5597694292890039590815057 4198270719667529693111293)
                      ·
                        rfl

theorem cell23_8176103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_8176103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176103 prefixEnd_8176103 := by exact prefixLift 8176103
  have htrace : WordTrace (prefixWord ++ tailWord_8176103) baseStart_8176103 baseEnd_8176103 := by
    simpa [prefixWord, tailWord_8176103, baseEnd_8176103] using wordTrace_append hprefix tailTrace_8176103
  have hstable : (prefixWord ++ tailWord_8176103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176103).length < 2 ^ (prefixWord ++ tailWord_8176103).sum := by decide
  have hdescent : baseEnd_8176103 < baseStart_8176103 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176109 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 9]
def baseStart_8176109 : Nat := 118140960795 + 8176109 * 2 ^ 59
def prefixEnd_8176109 : Nat := 4983230072969 + 3 ^ 40 * 8176109 * 2
def baseEnd_8176109 : Nat := 466474866727939629959585

theorem tailTrace_8176109 : CollatzResearch.WordTrace tailWord_8176109 prefixEnd_8176109 466474866727939629959585 := by
  unfold tailWord_8176109
  simp only [CollatzResearch.WordTrace]
  refine ⟨298207193936360936091755381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198804795957573957394503587 298207193936360936091755381)
  ·
    refine ⟨27956924431533837758602067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 298207193936360936091755381 27956924431533837758602067)
    ·
      refine ⟨41935386647300756637903101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27956924431533837758602067 41935386647300756637903101)
      ·
        refine ⟨15725769992737783739213663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41935386647300756637903101 15725769992737783739213663)
        ·
          refine ⟨23588654989106675608820495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15725769992737783739213663 23588654989106675608820495)
          ·
            refine ⟨35382982483660013413230743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23588654989106675608820495 35382982483660013413230743)
            ·
              refine ⟨53074473725490020119846115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35382982483660013413230743 53074473725490020119846115)
              ·
                refine ⟨79611710588235030179769173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53074473725490020119846115 79611710588235030179769173)
                ·
                  refine ⟨466474866727939629959585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79611710588235030179769173 466474866727939629959585)
                  ·
                    rfl

theorem cell23_8176109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_8176109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176109 prefixEnd_8176109 := by exact prefixLift 8176109
  have htrace : WordTrace (prefixWord ++ tailWord_8176109) baseStart_8176109 baseEnd_8176109 := by
    simpa [prefixWord, tailWord_8176109, baseEnd_8176109] using wordTrace_append hprefix tailTrace_8176109
  have hstable : (prefixWord ++ tailWord_8176109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176109).length < 2 ^ (prefixWord ++ tailWord_8176109).sum := by decide
  have hdescent : baseEnd_8176109 < baseStart_8176109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176179 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 3]
def baseStart_8176179 : Nat := 118140960795 + 8176179 * 2 ^ 59
def prefixEnd_8176179 : Nat := 4983230072969 + 3 ^ 40 * 8176179 * 2
def baseEnd_8176179 : Nat := 4198309744197271395760943

theorem tailTrace_8176179 : CollatzResearch.WordTrace tailWord_8176179 prefixEnd_8176179 4198309744197271395760943 := by
  unfold tailWord_8176179
  simp only [CollatzResearch.WordTrace]
  refine ⟨298209747046107338046803591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198806498030738225364535727 298209747046107338046803591)
  ·
    refine ⟨447314620569161007070205387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298209747046107338046803591 447314620569161007070205387)
    ·
      refine ⟨670971930853741510605308081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447314620569161007070205387 670971930853741510605308081)
      ·
        refine ⟨503228948140306132953981061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670971930853741510605308081 503228948140306132953981061)
        ·
          refine ⟨94355427776307399928871449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 503228948140306132953981061 94355427776307399928871449)
          ·
            refine ⟨70766570832230549946653587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94355427776307399928871449 70766570832230549946653587)
            ·
              refine ⟨106149856248345824919980381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70766570832230549946653587 106149856248345824919980381)
              ·
                refine ⟨39806196093129684344992643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106149856248345824919980381 39806196093129684344992643)
                ·
                  refine ⟨59709294139694526517488965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39806196093129684344992643 59709294139694526517488965)
                  ·
                    refine ⟨11195492651192723722029181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59709294139694526517488965 11195492651192723722029181)
                    ·
                      refine ⟨4198309744197271395760943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11195492651192723722029181 4198309744197271395760943)
                      ·
                        rfl

theorem cell23_8176179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 3].length) (baseStart_8176179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176179 prefixEnd_8176179 := by exact prefixLift 8176179
  have htrace : WordTrace (prefixWord ++ tailWord_8176179) baseStart_8176179 baseEnd_8176179 := by
    simpa [prefixWord, tailWord_8176179, baseEnd_8176179] using wordTrace_append hprefix tailTrace_8176179
  have hstable : (prefixWord ++ tailWord_8176179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176179).length < 2 ^ (prefixWord ++ tailWord_8176179).sum := by decide
  have hdescent : baseEnd_8176179 < baseStart_8176179 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176199 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 8]
def baseStart_8176199 : Nat := 118140960795 + 8176199 * 2 ^ 59
def prefixEnd_8176199 : Nat := 4983230072969 + 3 ^ 40 * 8176199 * 2
def baseEnd_8176199 : Nat := 466480001534484590834539

theorem tailTrace_8176199 : CollatzResearch.WordTrace tailWord_8176199 prefixEnd_8176199 466480001534484590834539 := by
  unfold tailWord_8176199
  simp only [CollatzResearch.WordTrace]
  refine ⟨298210476506034881462531651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198806984337356587641687767 298210476506034881462531651)
  ·
    refine ⟨447315714759052322193797477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298210476506034881462531651 447315714759052322193797477)
    ·
      refine ⟨83871696517322310411337027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447315714759052322193797477 83871696517322310411337027)
      ·
        refine ⟨125807544775983465617005541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83871696517322310411337027 125807544775983465617005541)
        ·
          refine ⟨23588914645496899803188539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125807544775983465617005541 23588914645496899803188539)
          ·
            refine ⟨35383371968245349704782809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23588914645496899803188539 35383371968245349704782809)
            ·
              refine ⟨26537528976184012278587107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35383371968245349704782809 26537528976184012278587107)
              ·
                refine ⟨39806293464276018417880661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26537528976184012278587107 39806293464276018417880661)
                ·
                  refine ⟨466480001534484590834539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39806293464276018417880661 466480001534484590834539)
                  ·
                    rfl

theorem cell23_8176199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 8].length) (baseStart_8176199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176199 prefixEnd_8176199 := by exact prefixLift 8176199
  have htrace : WordTrace (prefixWord ++ tailWord_8176199) baseStart_8176199 baseEnd_8176199 := by
    simpa [prefixWord, tailWord_8176199, baseEnd_8176199] using wordTrace_append hprefix tailTrace_8176199
  have hstable : (prefixWord ++ tailWord_8176199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176199).length < 2 ^ (prefixWord ++ tailWord_8176199).sum := by decide
  have hdescent : baseEnd_8176199 < baseStart_8176199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176216 : List Nat := [2, 1, 2, 2, 1, 2, 6, 1, 6]
def baseStart_8176216 : Nat := 118140960795 + 8176216 * 2 ^ 59
def prefixEnd_8176216 : Nat := 4983230072969 + 3 ^ 40 * 8176216 * 2
def baseEnd_8176216 : Nat := 466480971442387527888697

theorem tailTrace_8176216 : CollatzResearch.WordTrace tailWord_8176216 prefixEnd_8176216 466480971442387527888697 := by
  unfold tailWord_8176216
  simp only [CollatzResearch.WordTrace]
  refine ⟨149105548273486646682950251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198807397697982195577267001 149105548273486646682950251)
  ·
    refine ⟨223658322410229970024425377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149105548273486646682950251 223658322410229970024425377)
    ·
      refine ⟨167743741807672477518319033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223658322410229970024425377 167743741807672477518319033)
      ·
        refine ⟨125807806355754358138739275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167743741807672477518319033 125807806355754358138739275)
        ·
          refine ⟨188711709533631537208108913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125807806355754358138739275 188711709533631537208108913)
          ·
            refine ⟨141533782150223652906081685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188711709533631537208108913 141533782150223652906081685)
            ·
              refine ⟨6634396038291733729972579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141533782150223652906081685 6634396038291733729972579)
              ·
                refine ⟨9951594057437600594958869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6634396038291733729972579 9951594057437600594958869)
                ·
                  refine ⟨466480971442387527888697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9951594057437600594958869 466480971442387527888697)
                  ·
                    rfl

theorem cell23_8176216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 6].length) (baseStart_8176216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176216 prefixEnd_8176216 := by exact prefixLift 8176216
  have htrace : WordTrace (prefixWord ++ tailWord_8176216) baseStart_8176216 baseEnd_8176216 := by
    simpa [prefixWord, tailWord_8176216, baseEnd_8176216] using wordTrace_append hprefix tailTrace_8176216
  have hstable : (prefixWord ++ tailWord_8176216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176216).length < 2 ^ (prefixWord ++ tailWord_8176216).sum := by decide
  have hdescent : baseEnd_8176216 < baseStart_8176216 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176236 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 1, 5, 2]
def baseStart_8176236 : Nat := 118140960795 + 8176236 * 2 ^ 59
def prefixEnd_8176236 : Nat := 4983230072969 + 3 ^ 40 * 8176236 * 2
def baseEnd_8176236 : Nat := 4198339012594577672748181

theorem tailTrace_8176236 : CollatzResearch.WordTrace tailWord_8176236 prefixEnd_8176236 4198339012594577672748181 := by
  unfold tailWord_8176236
  simp only [CollatzResearch.WordTrace]
  refine ⟨149105913003450418390814281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198807884004600557854419041 149105913003450418390814281)
  ·
    refine ⟨111829434752587813793110711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149105913003450418390814281 111829434752587813793110711)
    ·
      refine ⟨167744152128881720689666067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111829434752587813793110711 167744152128881720689666067)
      ·
        refine ⟨251616228193322581034499101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167744152128881720689666067 251616228193322581034499101)
        ·
          refine ⟨94356085572495967887937163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251616228193322581034499101 94356085572495967887937163)
          ·
            refine ⟨141534128358743951831905745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94356085572495967887937163 141534128358743951831905745)
            ·
              refine ⟨106150596269057963873929309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141534128358743951831905745 106150596269057963873929309)
              ·
                refine ⟨39806473600896736452723491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106150596269057963873929309 39806473600896736452723491)
                ·
                  refine ⟨59709710401345104679085237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39806473600896736452723491 59709710401345104679085237)
                  ·
                    refine ⟨5597785350126103563664241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59709710401345104679085237 5597785350126103563664241)
                    ·
                      refine ⟨4198339012594577672748181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5597785350126103563664241 4198339012594577672748181)
                      ·
                        rfl

theorem cell23_8176236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 5, 2].length) (baseStart_8176236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176236 prefixEnd_8176236 := by exact prefixLift 8176236
  have htrace : WordTrace (prefixWord ++ tailWord_8176236) baseStart_8176236 baseEnd_8176236 := by
    simpa [prefixWord, tailWord_8176236, baseEnd_8176236] using wordTrace_append hprefix tailTrace_8176236
  have hstable : (prefixWord ++ tailWord_8176236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176236).length < 2 ^ (prefixWord ++ tailWord_8176236).sum := by decide
  have hdescent : baseEnd_8176236 < baseStart_8176236 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176303 : List Nat := [1, 1, 2, 1, 2, 6, 1, 3, 1, 2, 3]
def baseStart_8176303 : Nat := 118140960795 + 8176303 * 2 ^ 59
def prefixEnd_8176303 : Nat := 4983230072969 + 3 ^ 40 * 8176303 * 2
def baseEnd_8176303 : Nat := 4198373415798428910610373

theorem tailTrace_8176303 : CollatzResearch.WordTrace tailWord_8176303 prefixEnd_8176303 4198373415798428910610373 := by
  unfold tailWord_8176303
  simp only [CollatzResearch.WordTrace]
  refine ⟨298214269697658107224317563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198809513131772071482878375 298214269697658107224317563)
  ·
    refine ⟨447321404546487160836476345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298214269697658107224317563 447321404546487160836476345)
    ·
      refine ⟨335491053409865370627357259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447321404546487160836476345 335491053409865370627357259)
      ·
        refine ⟨503236580114798055941035889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335491053409865370627357259 503236580114798055941035889)
        ·
          refine ⟨377427435086098541955776917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503236580114798055941035889 377427435086098541955776917)
          ·
            refine ⟨17691911019660869154177043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 377427435086098541955776917 17691911019660869154177043)
            ·
              refine ⟨26537866529491303731265565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17691911019660869154177043 26537866529491303731265565)
              ·
                refine ⟨9951699948559238899224587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26537866529491303731265565 9951699948559238899224587)
                ·
                  refine ⟨14927549922838858348836881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9951699948559238899224587 14927549922838858348836881)
                  ·
                    refine ⟨11195662442129143761627661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14927549922838858348836881 11195662442129143761627661)
                    ·
                      refine ⟨4198373415798428910610373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11195662442129143761627661 4198373415798428910610373)
                      ·
                        rfl

theorem cell23_8176303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 2, 3].length) (baseStart_8176303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176303 prefixEnd_8176303 := by exact prefixLift 8176303
  have htrace : WordTrace (prefixWord ++ tailWord_8176303) baseStart_8176303 baseEnd_8176303 := by
    simpa [prefixWord, tailWord_8176303, baseEnd_8176303] using wordTrace_append hprefix tailTrace_8176303
  have hstable : (prefixWord ++ tailWord_8176303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176303).length < 2 ^ (prefixWord ++ tailWord_8176303).sum := by decide
  have hdescent : baseEnd_8176303 < baseStart_8176303 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176317 : List Nat := [1, 4, 1, 2, 1, 3, 2, 4, 1, 2, 2]
def baseStart_8176317 : Nat := 118140960795 + 8176317 * 2 ^ 59
def prefixEnd_8176317 : Nat := 4983230072969 + 3 ^ 40 * 8176317 * 2
def baseEnd_8176317 : Nat := 4198380604527591855835309

theorem tailTrace_8176317 : CollatzResearch.WordTrace tailWord_8176317 prefixEnd_8176317 4198380604527591855835309 := by
  unfold tailWord_8176317
  simp only [CollatzResearch.WordTrace]
  refine ⟨298214780319607387615327205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198809853546404925076884803 298214780319607387615327205)
  ·
    refine ⟨55915271309926385177873851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298214780319607387615327205 55915271309926385177873851)
    ·
      refine ⟨83872906964889577766810777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55915271309926385177873851 83872906964889577766810777)
      ·
        refine ⟨62904680223667183325108083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83872906964889577766810777 62904680223667183325108083)
        ·
          refine ⟨94357020335500774987662125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62904680223667183325108083 94357020335500774987662125)
          ·
            refine ⟨35383882625812790620373297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94357020335500774987662125 35383882625812790620373297)
            ·
              refine ⟨26537911969359592965279973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35383882625812790620373297 26537911969359592965279973)
              ·
                refine ⟨4975858494254923680989995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26537911969359592965279973 4975858494254923680989995)
                ·
                  refine ⟨7463787741382385521484993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4975858494254923680989995 7463787741382385521484993)
                  ·
                    refine ⟨5597840806036789141113745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7463787741382385521484993 5597840806036789141113745)
                    ·
                      refine ⟨4198380604527591855835309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5597840806036789141113745 4198380604527591855835309)
                      ·
                        rfl

theorem cell23_8176317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_8176317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176317 prefixEnd_8176317 := by exact prefixLift 8176317
  have htrace : WordTrace (prefixWord ++ tailWord_8176317) baseStart_8176317 baseEnd_8176317 := by
    simpa [prefixWord, tailWord_8176317, baseEnd_8176317] using wordTrace_append hprefix tailTrace_8176317
  have hstable : (prefixWord ++ tailWord_8176317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176317).length < 2 ^ (prefixWord ++ tailWord_8176317).sum := by decide
  have hdescent : baseEnd_8176317 < baseStart_8176317 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176329 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 6, 2, 5]
def baseStart_8176329 : Nat := 118140960795 + 8176329 * 2 ^ 59
def prefixEnd_8176329 : Nat := 4983230072969 + 3 ^ 40 * 8176329 * 2
def baseEnd_8176329 : Nat := 4198386766295445808885253

theorem tailTrace_8176329 : CollatzResearch.WordTrace tailWord_8176329 prefixEnd_8176329 4198386766295445808885253 := by
  unfold tailWord_8176329
  simp only [CollatzResearch.WordTrace]
  refine ⟨298215217995563913664764041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198810145330375942443176027 298215217995563913664764041)
  ·
    refine ⟨223661413496672935248573031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298215217995563913664764041 223661413496672935248573031)
    ·
      refine ⟨335492120245009402872859547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223661413496672935248573031 335492120245009402872859547)
      ·
        refine ⟨503238180367514104309289321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335492120245009402872859547 503238180367514104309289321)
        ·
          refine ⟨377428635275635578231966991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503238180367514104309289321 377428635275635578231966991)
          ·
            refine ⟨566142952913453367347950487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377428635275635578231966991 566142952913453367347950487)
            ·
              refine ⟨849214429370180051021925731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566142952913453367347950487 849214429370180051021925731)
              ·
                refine ⟨1273821644055270076532888597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849214429370180051021925731 1273821644055270076532888597)
                ·
                  refine ⟨59710389565090784837479153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1273821644055270076532888597 59710389565090784837479153)
                  ·
                    refine ⟨44782792173818088628109365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59710389565090784837479153 44782792173818088628109365)
                    ·
                      refine ⟨4198386766295445808885253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44782792173818088628109365 4198386766295445808885253)
                      ·
                        rfl

theorem cell23_8176329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_8176329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176329 prefixEnd_8176329 := by exact prefixLift 8176329
  have htrace : WordTrace (prefixWord ++ tailWord_8176329) baseStart_8176329 baseEnd_8176329 := by
    simpa [prefixWord, tailWord_8176329, baseEnd_8176329] using wordTrace_append hprefix tailTrace_8176329
  have hstable : (prefixWord ++ tailWord_8176329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176329).length < 2 ^ (prefixWord ++ tailWord_8176329).sum := by decide
  have hdescent : baseEnd_8176329 < baseStart_8176329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176340 : List Nat := [2, 4, 1, 3, 2, 2, 2, 7]
def baseStart_8176340 : Nat := 118140960795 + 8176340 * 2 ^ 59
def prefixEnd_8176340 : Nat := 4983230072969 + 3 ^ 40 * 8176340 * 2
def baseEnd_8176340 : Nat := 155496015354912787623989

theorem tailTrace_8176340 : CollatzResearch.WordTrace tailWord_8176340 prefixEnd_8176340 155496015354912787623989 := by
  unfold tailWord_8176340
  simp only [CollatzResearch.WordTrace]
  refine ⟨149107809599262031271707237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198810412799016041695609649 149107809599262031271707237)
  ·
    refine ⟨27957714299861630863445107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149107809599262031271707237 27957714299861630863445107)
    ·
      refine ⟨41936571449792446295167661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27957714299861630863445107 41936571449792446295167661)
      ·
        refine ⟨15726214293672167360687873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41936571449792446295167661 15726214293672167360687873)
        ·
          refine ⟨11794660720254125520515905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15726214293672167360687873 11794660720254125520515905)
          ·
            refine ⟨8845995540190594140386929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11794660720254125520515905 8845995540190594140386929)
            ·
              refine ⟨6634496655142945605290197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8845995540190594140386929 6634496655142945605290197)
              ·
                refine ⟨155496015354912787623989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6634496655142945605290197 155496015354912787623989)
                ·
                  rfl

theorem cell23_8176340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 7].length) (baseStart_8176340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176340 prefixEnd_8176340 := by exact prefixLift 8176340
  have htrace : WordTrace (prefixWord ++ tailWord_8176340) baseStart_8176340 baseEnd_8176340 := by
    simpa [prefixWord, tailWord_8176340, baseEnd_8176340] using wordTrace_append hprefix tailTrace_8176340
  have hstable : (prefixWord ++ tailWord_8176340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176340).length < 2 ^ (prefixWord ++ tailWord_8176340).sum := by decide
  have hdescent : baseEnd_8176340 < baseStart_8176340 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176376 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 2, 4, 3]
def baseStart_8176376 : Nat := 118140960795 + 8176376 * 2 ^ 59
def prefixEnd_8176376 : Nat := 4983230072969 + 3 ^ 40 * 8176376 * 2
def baseEnd_8176376 : Nat := 4198410899886207124997537

theorem tailTrace_8176376 : CollatzResearch.WordTrace tailWord_8176376 prefixEnd_8176376 4198410899886207124997537 := by
  unfold tailWord_8176376
  simp only [CollatzResearch.WordTrace]
  refine ⟨149108466113196820345862491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198811288150929093794483321 149108466113196820345862491)
  ·
    refine ⟨223662699169795230518793737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149108466113196820345862491 223662699169795230518793737)
    ·
      refine ⟨167747024377346422889095303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223662699169795230518793737 167747024377346422889095303)
      ·
        refine ⟨251620536566019634333642955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167747024377346422889095303 251620536566019634333642955)
        ·
          refine ⟨377430804849029451500464433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251620536566019634333642955 377430804849029451500464433)
          ·
            refine ⟨283073103636772088625348325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377430804849029451500464433 283073103636772088625348325)
            ·
              refine ⟨53076206931894766617252811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 283073103636772088625348325 53076206931894766617252811)
              ·
                refine ⟨79614310397842149925879217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53076206931894766617252811 79614310397842149925879217)
                ·
                  refine ⟨59710732798381612444409413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79614310397842149925879217 59710732798381612444409413)
                  ·
                    refine ⟨11195762399696552333326765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59710732798381612444409413 11195762399696552333326765)
                    ·
                      refine ⟨4198410899886207124997537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11195762399696552333326765 4198410899886207124997537)
                      ·
                        rfl

theorem cell23_8176376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_8176376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176376 prefixEnd_8176376 := by exact prefixLift 8176376
  have htrace : WordTrace (prefixWord ++ tailWord_8176376) baseStart_8176376 baseEnd_8176376 := by
    simpa [prefixWord, tailWord_8176376, baseEnd_8176376] using wordTrace_append hprefix tailTrace_8176376
  have hstable : (prefixWord ++ tailWord_8176376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176376).length < 2 ^ (prefixWord ++ tailWord_8176376).sum := by decide
  have hdescent : baseEnd_8176376 < baseStart_8176376 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176433 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 1, 7, 2]
def baseStart_8176433 : Nat := 118140960795 + 8176433 * 2 ^ 59
def prefixEnd_8176433 : Nat := 4983230072969 + 3 ^ 40 * 8176433 * 2
def baseEnd_8176433 : Nat := 4198440168283513401984775

theorem tailTrace_8176433 : CollatzResearch.WordTrace tailWord_8176433 prefixEnd_8176433 4198440168283513401984775 := by
  unfold tailWord_8176433
  simp only [CollatzResearch.WordTrace]
  refine ⟨298219011187187139426549953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198812674124791426284366635 298219011187187139426549953)
  ·
    refine ⟨223664258390390354569912465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298219011187187139426549953 223664258390390354569912465)
    ·
      refine ⟨167748193792792765927434349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223664258390390354569912465 167748193792792765927434349)
      ·
        refine ⟨62905572672297287222787881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167748193792792765927434349 62905572672297287222787881)
        ·
          refine ⟨47179179504222965417090911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62905572672297287222787881 47179179504222965417090911)
          ·
            refine ⟨70768769256334448125636367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47179179504222965417090911 70768769256334448125636367)
            ·
              refine ⟨106153153884501672188454551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70768769256334448125636367 106153153884501672188454551)
              ·
                refine ⟨159229730826752508282681827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106153153884501672188454551 159229730826752508282681827)
                ·
                  refine ⟨238844596240128762424022741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159229730826752508282681827 238844596240128762424022741)
                  ·
                    refine ⟨5597920224378017869313033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 238844596240128762424022741 5597920224378017869313033)
                    ·
                      refine ⟨4198440168283513401984775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5597920224378017869313033 4198440168283513401984775)
                      ·
                        rfl

theorem cell23_8176433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_8176433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176433 prefixEnd_8176433 := by exact prefixLift 8176433
  have htrace : WordTrace (prefixWord ++ tailWord_8176433) baseStart_8176433 baseEnd_8176433 := by
    simpa [prefixWord, tailWord_8176433, baseEnd_8176433] using wordTrace_append hprefix tailTrace_8176433
  have hstable : (prefixWord ++ tailWord_8176433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176433).length < 2 ^ (prefixWord ++ tailWord_8176433).sum := by decide
  have hdescent : baseEnd_8176433 < baseStart_8176433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176460 : List Nat := [2, 2, 1, 3, 3, 3, 1, 1, 2, 5]
def baseStart_8176460 : Nat := 118140960795 + 8176460 * 2 ^ 59
def prefixEnd_8176460 : Nat := 4983230072969 + 3 ^ 40 * 8176460 * 2
def baseEnd_8176460 : Nat := 1399484677420394932115717

theorem tailTrace_8176460 : CollatzResearch.WordTrace tailWord_8176460 prefixEnd_8176460 1399484677420394932115717 := by
  unfold tailWord_8176460
  simp only [CollatzResearch.WordTrace]
  refine ⟨149109997979044661518891417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198813330638726215358521889 149109997979044661518891417)
  ·
    refine ⟨111832498484283496139168563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149109997979044661518891417 111832498484283496139168563)
    ·
      refine ⟨167748747726425244208752845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111832498484283496139168563 167748747726425244208752845)
      ·
        refine ⟨62905780397409466578282317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167748747726425244208752845 62905780397409466578282317)
        ·
          refine ⟨23589667649028549966855869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62905780397409466578282317 23589667649028549966855869)
          ·
            refine ⟨8846125368385706237570951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23589667649028549966855869 8846125368385706237570951)
            ·
              refine ⟨13269188052578559356356427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8846125368385706237570951 13269188052578559356356427)
              ·
                refine ⟨19903782078867839034534641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13269188052578559356356427 19903782078867839034534641)
                ·
                  refine ⟨14927836559150879275900981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19903782078867839034534641 14927836559150879275900981)
                  ·
                    refine ⟨1399484677420394932115717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14927836559150879275900981 1399484677420394932115717)
                    ·
                      rfl

theorem cell23_8176460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 2, 5].length) (baseStart_8176460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176460 prefixEnd_8176460 := by exact prefixLift 8176460
  have htrace : WordTrace (prefixWord ++ tailWord_8176460) baseStart_8176460 baseEnd_8176460 := by
    simpa [prefixWord, tailWord_8176460, baseEnd_8176460] using wordTrace_append hprefix tailTrace_8176460
  have hstable : (prefixWord ++ tailWord_8176460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176460).length < 2 ^ (prefixWord ++ tailWord_8176460).sum := by decide
  have hdescent : baseEnd_8176460 < baseStart_8176460 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176506 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6]
def baseStart_8176506 : Nat := 118140960795 + 8176506 * 2 ^ 59
def prefixEnd_8176506 : Nat := 4983230072969 + 3 ^ 40 * 8176506 * 2
def baseEnd_8176506 : Nat := 4198477652371291616371939

theorem tailTrace_8176506 : CollatzResearch.WordTrace tailWord_8176506 prefixEnd_8176506 4198477652371291616371939 := by
  unfold tailWord_8176506
  simp only [CollatzResearch.WordTrace]
  refine ⟨74555418428980668223489343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198814449143948448595971581 74555418428980668223489343)
  ·
    refine ⟨111833127643471002335234015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74555418428980668223489343 111833127643471002335234015)
    ·
      refine ⟨167749691465206503502851023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111833127643471002335234015 167749691465206503502851023)
      ·
        refine ⟨251624537197809755254276535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167749691465206503502851023 251624537197809755254276535)
        ·
          refine ⟨377436805796714632881414803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251624537197809755254276535 377436805796714632881414803)
          ·
            refine ⟨566155208695071949322122205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377436805796714632881414803 566155208695071949322122205)
            ·
              refine ⟨212308203260651980995795827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 566155208695071949322122205 212308203260651980995795827)
              ·
                refine ⟨318462304890977971493693741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212308203260651980995795827 318462304890977971493693741)
                ·
                  refine ⟨119423364334116739310135153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 318462304890977971493693741 119423364334116739310135153)
                  ·
                    refine ⟨89567523250587554482601365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119423364334116739310135153 89567523250587554482601365)
                    ·
                      refine ⟨4198477652371291616371939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89567523250587554482601365 4198477652371291616371939)
                      ·
                        rfl

theorem cell23_8176506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_8176506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176506 prefixEnd_8176506 := by exact prefixLift 8176506
  have htrace : WordTrace (prefixWord ++ tailWord_8176506) baseStart_8176506 baseEnd_8176506 := by
    simpa [prefixWord, tailWord_8176506, baseEnd_8176506] using wordTrace_append hprefix tailTrace_8176506
  have hstable : (prefixWord ++ tailWord_8176506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176506).length < 2 ^ (prefixWord ++ tailWord_8176506).sum := by decide
  have hdescent : baseEnd_8176506 < baseStart_8176506 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176534 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_8176534 : Nat := 118140960795 + 8176534 * 2 ^ 59
def prefixEnd_8176534 : Nat := 4983230072969 + 3 ^ 40 * 8176534 * 2
def baseEnd_8176534 : Nat := 4198492029829617506821811

theorem tailTrace_8176534 : CollatzResearch.WordTrace tailWord_8176534 prefixEnd_8176534 4198492029829617506821811 := by
  unfold tailWord_8176534
  simp only [CollatzResearch.WordTrace]
  refine ⟨18638918434988827104748541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198815129973214155783984437 18638918434988827104748541)
  ·
    refine ⟨6989594413120810164280703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18638918434988827104748541 6989594413120810164280703)
    ·
      refine ⟨10484391619681215246421055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6989594413120810164280703 10484391619681215246421055)
      ·
        refine ⟨15726587429521822869631583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10484391619681215246421055 15726587429521822869631583)
        ·
          refine ⟨23589881144282734304447375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15726587429521822869631583 23589881144282734304447375)
          ·
            refine ⟨35384821716424101456671063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23589881144282734304447375 35384821716424101456671063)
            ·
              refine ⟨53077232574636152185006595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35384821716424101456671063 53077232574636152185006595)
              ·
                refine ⟨79615848861954228277509893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53077232574636152185006595 79615848861954228277509893)
                ·
                  refine ⟨14927971661616417802033105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79615848861954228277509893 14927971661616417802033105)
                  ·
                    refine ⟨11195978746212313351524829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14927971661616417802033105 11195978746212313351524829)
                    ·
                      refine ⟨4198492029829617506821811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11195978746212313351524829 4198492029829617506821811)
                      ·
                        rfl

theorem cell23_8176534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_8176534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176534 prefixEnd_8176534 := by exact prefixLift 8176534
  have htrace : WordTrace (prefixWord ++ tailWord_8176534) baseStart_8176534 baseEnd_8176534 := by
    simpa [prefixWord, tailWord_8176534, baseEnd_8176534] using wordTrace_append hprefix tailTrace_8176534
  have hstable : (prefixWord ++ tailWord_8176534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176534).length < 2 ^ (prefixWord ++ tailWord_8176534).sum := by decide
  have hdescent : baseEnd_8176534 < baseStart_8176534 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176547 : List Nat := [1, 1, 1, 4, 1, 2, 2, 6, 1, 1, 3]
def baseStart_8176547 : Nat := 118140960795 + 8176547 * 2 ^ 59
def prefixEnd_8176547 : Nat := 4983230072969 + 3 ^ 40 * 8176547 * 2
def baseEnd_8176547 : Nat := 4198498705078125955959251

theorem tailTrace_8176547 : CollatzResearch.WordTrace tailWord_8176547 prefixEnd_8176547 4198498705078125955959251 := by
  unfold tailWord_8176547
  simp only [CollatzResearch.WordTrace]
  refine ⟨298223169108774136896199895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198815446072516091264133263 298223169108774136896199895)
  ·
    refine ⟨447334753663161205344299843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298223169108774136896199895 447334753663161205344299843)
    ·
      refine ⟨671002130494741808016449765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447334753663161205344299843 671002130494741808016449765)
      ·
        refine ⟨125812899467764089003084331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 671002130494741808016449765 125812899467764089003084331)
        ·
          refine ⟨188719349201646133504626497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125812899467764089003084331 188719349201646133504626497)
          ·
            refine ⟨141539511901234600128469873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188719349201646133504626497 141539511901234600128469873)
            ·
              refine ⟨106154633925925950096352405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141539511901234600128469873 106154633925925950096352405)
              ·
                refine ⟨4975998465277778910766519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106154633925925950096352405 4975998465277778910766519)
                ·
                  refine ⟨7463997697916668366149779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4975998465277778910766519 7463997697916668366149779)
                  ·
                    refine ⟨11195996546875002549224669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7463997697916668366149779 11195996546875002549224669)
                    ·
                      refine ⟨4198498705078125955959251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11195996546875002549224669 4198498705078125955959251)
                      ·
                        rfl

theorem cell23_8176547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 1, 1, 3].length) (baseStart_8176547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176547 prefixEnd_8176547 := by exact prefixLift 8176547
  have htrace : WordTrace (prefixWord ++ tailWord_8176547) baseStart_8176547 baseEnd_8176547 := by
    simpa [prefixWord, tailWord_8176547, baseEnd_8176547] using wordTrace_append hprefix tailTrace_8176547
  have hstable : (prefixWord ++ tailWord_8176547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176547).length < 2 ^ (prefixWord ++ tailWord_8176547).sum := by decide
  have hdescent : baseEnd_8176547 < baseStart_8176547 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176553 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 3, 1, 4]
def baseStart_8176553 : Nat := 118140960795 + 8176553 * 2 ^ 59
def prefixEnd_8176553 : Nat := 4983230072969 + 3 ^ 40 * 8176553 * 2
def baseEnd_8176553 : Nat := 4198501785962052932484223

theorem tailTrace_8176553 : CollatzResearch.WordTrace tailWord_8176553 prefixEnd_8176553 4198501785962052932484223 := by
  unfold tailWord_8176553
  simp only [CollatzResearch.WordTrace]
  refine ⟨298223387946752399920918313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198815591964501599947278875 298223387946752399920918313)
  ·
    refine ⟨223667540960064299940688735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298223387946752399920918313 223667540960064299940688735)
    ·
      refine ⟨335501311440096449911033103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223667540960064299940688735 335501311440096449911033103)
      ·
        refine ⟨503251967160144674866549655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335501311440096449911033103 503251967160144674866549655)
        ·
          refine ⟨754877950740217012299824483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503251967160144674866549655 754877950740217012299824483)
          ·
            refine ⟨1132316926110325518449736725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754877950740217012299824483 1132316926110325518449736725)
            ·
              refine ⟨53077355911421508677331409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1132316926110325518449736725 53077355911421508677331409)
              ·
                refine ⟨39808016933566131507998557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53077355911421508677331409 39808016933566131507998557)
                ·
                  refine ⟨14928006350087299315499459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39808016933566131507998557 14928006350087299315499459)
                  ·
                    refine ⟨22392009525130948973249189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14928006350087299315499459 22392009525130948973249189)
                    ·
                      refine ⟨4198501785962052932484223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22392009525130948973249189 4198501785962052932484223)
                      ·
                        rfl

theorem cell23_8176553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 1, 4].length) (baseStart_8176553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176553 prefixEnd_8176553 := by exact prefixLift 8176553
  have htrace : WordTrace (prefixWord ++ tailWord_8176553) baseStart_8176553 baseEnd_8176553 := by
    simpa [prefixWord, tailWord_8176553, baseEnd_8176553] using wordTrace_append hprefix tailTrace_8176553
  have hstable : (prefixWord ++ tailWord_8176553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176553).length < 2 ^ (prefixWord ++ tailWord_8176553).sum := by decide
  have hdescent : baseEnd_8176553 < baseStart_8176553 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176563 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 6, 4]
def baseStart_8176563 : Nat := 118140960795 + 8176563 * 2 ^ 59
def prefixEnd_8176563 : Nat := 4983230072969 + 3 ^ 40 * 8176563 * 2
def baseEnd_8176563 : Nat := 1399502306922865964453059

theorem tailTrace_8176563 : CollatzResearch.WordTrace tailWord_8176563 prefixEnd_8176563 1399502306922865964453059 := by
  unfold tailWord_8176563
  simp only [CollatzResearch.WordTrace]
  refine ⟨298223752676716171628782343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198815835117810781085854895 298223752676716171628782343)
  ·
    refine ⟨447335629015074257443173515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298223752676716171628782343 447335629015074257443173515)
    ·
      refine ⟨671003443522611386164760273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447335629015074257443173515 671003443522611386164760273)
      ·
        refine ⟨503252582641958539623570205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 671003443522611386164760273 503252582641958539623570205)
        ·
          refine ⟨188719718490734452358838827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 503252582641958539623570205 188719718490734452358838827)
          ·
            refine ⟨283079577736101678538258241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188719718490734452358838827 283079577736101678538258241)
            ·
              refine ⟨212309683302076258903693681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283079577736101678538258241 212309683302076258903693681)
              ·
                refine ⟨159232262476557194177770261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212309683302076258903693681 159232262476557194177770261)
                ·
                  refine ⟨7464012303588618477082981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159232262476557194177770261 7464012303588618477082981)
                  ·
                    refine ⟨1399502306922865964453059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7464012303588618477082981 1399502306922865964453059)
                    ·
                      rfl

theorem cell23_8176563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 4].length) (baseStart_8176563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176563 prefixEnd_8176563 := by exact prefixLift 8176563
  have htrace : WordTrace (prefixWord ++ tailWord_8176563) baseStart_8176563 baseEnd_8176563 := by
    simpa [prefixWord, tailWord_8176563, baseEnd_8176563] using wordTrace_append hprefix tailTrace_8176563
  have hstable : (prefixWord ++ tailWord_8176563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176563).length < 2 ^ (prefixWord ++ tailWord_8176563).sum := by decide
  have hdescent : baseEnd_8176563 < baseStart_8176563 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176583 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_8176583 : Nat := 118140960795 + 8176583 * 2 ^ 59
def prefixEnd_8176583 : Nat := 4983230072969 + 3 ^ 40 * 8176583 * 2
def baseEnd_8176583 : Nat := 4198517190381687815109085

theorem tailTrace_8176583 : CollatzResearch.WordTrace tailWord_8176583 prefixEnd_8176583 4198517190381687815109085 := by
  unfold tailWord_8176583
  simp only [CollatzResearch.WordTrace]
  refine ⟨298224482136643715044510403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198816321424429143363006935 298224482136643715044510403)
  ·
    refine ⟨447336723204965572566765605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298224482136643715044510403 447336723204965572566765605)
    ·
      refine ⟨83875635600931044856268551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447336723204965572566765605 83875635600931044856268551)
      ·
        refine ⟨125813453401396567284402827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83875635600931044856268551 125813453401396567284402827)
        ·
          refine ⟨188720180102094850926604241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125813453401396567284402827 188720180102094850926604241)
          ·
            refine ⟨141540135076571138194953181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188720180102094850926604241 141540135076571138194953181)
            ·
              refine ⟨53077550653714176823107443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141540135076571138194953181 53077550653714176823107443)
              ·
                refine ⟨79616325980571265234661165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53077550653714176823107443 79616325980571265234661165)
                ·
                  refine ⟨29856122242714224462997937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79616325980571265234661165 29856122242714224462997937)
                  ·
                    refine ⟨22392091682035668347248453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29856122242714224462997937 22392091682035668347248453)
                    ·
                      refine ⟨4198517190381687815109085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22392091682035668347248453 4198517190381687815109085)
                      ·
                        rfl

theorem cell23_8176583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_8176583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176583 prefixEnd_8176583 := by exact prefixLift 8176583
  have htrace : WordTrace (prefixWord ++ tailWord_8176583) baseStart_8176583 baseEnd_8176583 := by
    simpa [prefixWord, tailWord_8176583, baseEnd_8176583] using wordTrace_append hprefix tailTrace_8176583
  have hstable : (prefixWord ++ tailWord_8176583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176583).length < 2 ^ (prefixWord ++ tailWord_8176583).sum := by decide
  have hdescent : baseEnd_8176583 < baseStart_8176583 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176587 : List Nat := [1, 1, 1, 1, 3, 6, 3, 1, 1, 1, 4]
def baseStart_8176587 : Nat := 118140960795 + 8176587 * 2 ^ 59
def prefixEnd_8176587 : Nat := 4983230072969 + 3 ^ 40 * 8176587 * 2
def baseEnd_8176587 : Nat := 4198519244304305799459067

theorem tailTrace_8176587 : CollatzResearch.WordTrace tailWord_8176587 prefixEnd_8176587 4198519244304305799459067 := by
  unfold tailWord_8176587
  simp only [CollatzResearch.WordTrace]
  refine ⟨298224628028629223727656015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198816418685752815818437343 298224628028629223727656015)
  ·
    refine ⟨447336942042943835591484023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298224628028629223727656015 447336942042943835591484023)
    ·
      refine ⟨671005413064415753387226035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447336942042943835591484023 671005413064415753387226035)
      ·
        refine ⟨1006508119596623630080839053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671005413064415753387226035 1006508119596623630080839053)
        ·
          refine ⟨377440544848733861280314645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1006508119596623630080839053 377440544848733861280314645)
          ·
            refine ⟨17692525539784399747514749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 377440544848733861280314645 17692525539784399747514749)
            ·
              refine ⟨6634697077419149905318031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17692525539784399747514749 6634697077419149905318031)
              ·
                refine ⟨9952045616128724857977047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6634697077419149905318031 9952045616128724857977047)
                ·
                  refine ⟨14928068424193087286965571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9952045616128724857977047 14928068424193087286965571)
                  ·
                    refine ⟨22392102636289630930448357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14928068424193087286965571 22392102636289630930448357)
                    ·
                      refine ⟨4198519244304305799459067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22392102636289630930448357 4198519244304305799459067)
                      ·
                        rfl

theorem cell23_8176587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 1, 1, 4].length) (baseStart_8176587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176587 prefixEnd_8176587 := by exact prefixLift 8176587
  have htrace : WordTrace (prefixWord ++ tailWord_8176587) baseStart_8176587 baseEnd_8176587 := by
    simpa [prefixWord, tailWord_8176587, baseEnd_8176587] using wordTrace_append hprefix tailTrace_8176587
  have hstable : (prefixWord ++ tailWord_8176587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176587).length < 2 ^ (prefixWord ++ tailWord_8176587).sum := by decide
  have hdescent : baseEnd_8176587 < baseStart_8176587 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176590 : List Nat := [4, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5]
def baseStart_8176590 : Nat := 118140960795 + 8176590 * 2 ^ 59
def prefixEnd_8176590 : Nat := 4983230072969 + 3 ^ 40 * 8176590 * 2
def baseEnd_8176590 : Nat := 4198520784746269287721553

theorem tailTrace_8176590 : CollatzResearch.WordTrace tailWord_8176590 prefixEnd_8176590 4198520784746269287721553 := by
  unfold tailWord_8176590
  simp only [CollatzResearch.WordTrace]
  refine ⟨37278092180952294405001903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198816491631745570160010149 37278092180952294405001903)
  ·
    refine ⟨55917138271428441607502855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37278092180952294405001903 55917138271428441607502855)
    ·
      refine ⟨83875707407142662411254283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55917138271428441607502855 83875707407142662411254283)
      ·
        refine ⟨125813561110713993616881425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83875707407142662411254283 125813561110713993616881425)
        ·
          refine ⟨94360170833035495212661069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125813561110713993616881425 94360170833035495212661069)
          ·
            refine ⟨35385064062388310704747901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94360170833035495212661069 35385064062388310704747901)
            ·
              refine ⟨13269399023395616514280463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35385064062388310704747901 13269399023395616514280463)
              ·
                refine ⟨19904098535093424771420695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13269399023395616514280463 19904098535093424771420695)
                ·
                  refine ⟨29856147802640137157131043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19904098535093424771420695 29856147802640137157131043)
                  ·
                    refine ⟨44784221703960205735696565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29856147802640137157131043 44784221703960205735696565)
                    ·
                      refine ⟨4198520784746269287721553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44784221703960205735696565 4198520784746269287721553)
                      ·
                        rfl

theorem cell23_8176590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_8176590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176590 prefixEnd_8176590 := by exact prefixLift 8176590
  have htrace : WordTrace (prefixWord ++ tailWord_8176590) baseStart_8176590 baseEnd_8176590 := by
    simpa [prefixWord, tailWord_8176590, baseEnd_8176590] using wordTrace_append hprefix tailTrace_8176590
  have hstable : (prefixWord ++ tailWord_8176590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176590).length < 2 ^ (prefixWord ++ tailWord_8176590).sum := by decide
  have hdescent : baseEnd_8176590 < baseStart_8176590 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176598 : List Nat := [5, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3]
def baseStart_8176598 : Nat := 118140960795 + 8176598 * 2 ^ 59
def prefixEnd_8176598 : Nat := 4983230072969 + 3 ^ 40 * 8176598 * 2
def baseEnd_8176598 : Nat := 4198524892591505256421517

theorem tailTrace_8176598 : CollatzResearch.WordTrace tailWord_8176598 prefixEnd_8176598 4198524892591505256421517 := by
  unfold tailWord_8176598
  simp only [CollatzResearch.WordTrace]
  refine ⟨18639064326974335787894153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198816686154392915070870965 18639064326974335787894153)
  ·
    refine ⟨13979298245230751840920615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18639064326974335787894153 13979298245230751840920615)
    ·
      refine ⟨20968947367846127761380923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13979298245230751840920615 20968947367846127761380923)
      ·
        refine ⟨31453421051769191642071385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20968947367846127761380923 31453421051769191642071385)
        ·
          refine ⟨23590065788826893731553539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31453421051769191642071385 23590065788826893731553539)
          ·
            refine ⟨35385098683240340597330309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23590065788826893731553539 35385098683240340597330309)
            ·
              refine ⟨6634706003107563861999433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35385098683240340597330309 6634706003107563861999433)
              ·
                refine ⟨4976029502330672896499575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6634706003107563861999433 4976029502330672896499575)
                ·
                  refine ⟨7464044253496009344749363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4976029502330672896499575 7464044253496009344749363)
                  ·
                    refine ⟨11196066380244014017124045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7464044253496009344749363 11196066380244014017124045)
                    ·
                      refine ⟨4198524892591505256421517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11196066380244014017124045 4198524892591505256421517)
                      ·
                        rfl

theorem cell23_8176598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_8176598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176598 prefixEnd_8176598 := by exact prefixLift 8176598
  have htrace : WordTrace (prefixWord ++ tailWord_8176598) baseStart_8176598 baseEnd_8176598 := by
    simpa [prefixWord, tailWord_8176598, baseEnd_8176598] using wordTrace_append hprefix tailTrace_8176598
  have hstable : (prefixWord ++ tailWord_8176598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176598).length < 2 ^ (prefixWord ++ tailWord_8176598).sum := by decide
  have hdescent : baseEnd_8176598 < baseStart_8176598 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176620 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 3]
def baseStart_8176620 : Nat := 118140960795 + 8176620 * 2 ^ 59
def prefixEnd_8176620 : Nat := 4983230072969 + 3 ^ 40 * 8176620 * 2
def baseEnd_8176620 : Nat := 4198536189165904170346415

theorem tailTrace_8176620 : CollatzResearch.WordTrace tailWord_8176620 prefixEnd_8176620 4198536189165904170346415 := by
  unfold tailWord_8176620
  simp only [CollatzResearch.WordTrace]
  refine ⟨149112915818754835181803657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198817221091673113575738209 149112915818754835181803657)
  ·
    refine ⟨111834686864066126386352743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149112915818754835181803657 111834686864066126386352743)
    ·
      refine ⟨167752030296099189579529115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111834686864066126386352743 167752030296099189579529115)
      ·
        refine ⟨251628045444148784369293673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167752030296099189579529115 251628045444148784369293673)
        ·
          refine ⟨188721034083111588276970255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251628045444148784369293673 188721034083111588276970255)
          ·
            refine ⟨283081551124667382415455383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188721034083111588276970255 283081551124667382415455383)
            ·
              refine ⟨424622326687001073623183075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283081551124667382415455383 424622326687001073623183075)
              ·
                refine ⟨636933490030501610434774613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424622326687001073623183075 636933490030501610434774613)
                ·
                  refine ⟨7464064336294940747282515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 636933490030501610434774613 7464064336294940747282515)
                  ·
                    refine ⟨11196096504442411120923773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7464064336294940747282515 11196096504442411120923773)
                    ·
                      refine ⟨4198536189165904170346415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11196096504442411120923773 4198536189165904170346415)
                      ·
                        rfl

theorem cell23_8176620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 3].length) (baseStart_8176620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176620 prefixEnd_8176620 := by exact prefixLift 8176620
  have htrace : WordTrace (prefixWord ++ tailWord_8176620) baseStart_8176620 baseEnd_8176620 := by
    simpa [prefixWord, tailWord_8176620, baseEnd_8176620] using wordTrace_append hprefix tailTrace_8176620
  have hstable : (prefixWord ++ tailWord_8176620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176620).length < 2 ^ (prefixWord ++ tailWord_8176620).sum := by decide
  have hdescent : baseEnd_8176620 < baseStart_8176620 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176633 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 2, 2, 5]
def baseStart_8176633 : Nat := 118140960795 + 8176633 * 2 ^ 59
def prefixEnd_8176633 : Nat := 4983230072969 + 3 ^ 40 * 8176633 * 2
def baseEnd_8176633 : Nat := 4198542864414412619483855

theorem tailTrace_8176633 : CollatzResearch.WordTrace tailWord_8176633 prefixEnd_8176633 4198542864414412619483855 := by
  unfold tailWord_8176633
  simp only [CollatzResearch.WordTrace]
  refine ⟨298226305786462573583830553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198817537190975049055887035 298226305786462573583830553)
  ·
    refine ⟨223669729339846930187872915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298226305786462573583830553 223669729339846930187872915)
    ·
      refine ⟨335504594009770395281809373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223669729339846930187872915 335504594009770395281809373)
      ·
        refine ⟨125814222753663898230678515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335504594009770395281809373 125814222753663898230678515)
        ·
          refine ⟨188721334130495847346017773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125814222753663898230678515 188721334130495847346017773)
          ·
            refine ⟨70770500298935942754756665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188721334130495847346017773 70770500298935942754756665)
            ·
              refine ⟨53077875224201957066067499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70770500298935942754756665 53077875224201957066067499)
              ·
                refine ⟨79616812836302935599101249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53077875224201957066067499 79616812836302935599101249)
                ·
                  refine ⟨59712609627227201699325937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79616812836302935599101249 59712609627227201699325937)
                  ·
                    refine ⟨44784457220420401274494453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59712609627227201699325937 44784457220420401274494453)
                    ·
                      refine ⟨4198542864414412619483855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44784457220420401274494453 4198542864414412619483855)
                      ·
                        rfl

theorem cell23_8176633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_8176633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176633 prefixEnd_8176633 := by exact prefixLift 8176633
  have htrace : WordTrace (prefixWord ++ tailWord_8176633) baseStart_8176633 baseEnd_8176633 := by
    simpa [prefixWord, tailWord_8176633, baseEnd_8176633] using wordTrace_append hprefix tailTrace_8176633
  have hstable : (prefixWord ++ tailWord_8176633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176633).length < 2 ^ (prefixWord ++ tailWord_8176633).sum := by decide
  have hdescent : baseEnd_8176633 < baseStart_8176633 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176638 : List Nat := [4, 2, 2, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_8176638 : Nat := 118140960795 + 8176638 * 2 ^ 59
def prefixEnd_8176638 : Nat := 4983230072969 + 3 ^ 40 * 8176638 * 2
def baseEnd_8176638 : Nat := 4198545431817685099921333

theorem tailTrace_8176638 : CollatzResearch.WordTrace tailWord_8176638 prefixEnd_8176638 4198545431817685099921333 := by
  unfold tailWord_8176638
  simp only [CollatzResearch.WordTrace]
  refine ⟨37278311018930557429720321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198817658767629639625175045 37278311018930557429720321)
  ·
    refine ⟨27958733264197918072290241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37278311018930557429720321 27958733264197918072290241)
    ·
      refine ⟨20969049948148438554217681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27958733264197918072290241 20969049948148438554217681)
      ·
        refine ⟨15726787461111328915663261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20969049948148438554217681 15726787461111328915663261)
        ·
          refine ⟨5897545297916748343373723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15726787461111328915663261 5897545297916748343373723)
          ·
            refine ⟨8846317946875122515060585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5897545297916748343373723 8846317946875122515060585)
            ·
              refine ⟨6634738460156341886295439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8846317946875122515060585 6634738460156341886295439)
              ·
                refine ⟨9952107690234512829443159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6634738460156341886295439 9952107690234512829443159)
                ·
                  refine ⟨14928161535351769244164739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9952107690234512829443159 14928161535351769244164739)
                  ·
                    refine ⟨22392242303027653866247109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14928161535351769244164739 22392242303027653866247109)
                    ·
                      refine ⟨4198545431817685099921333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22392242303027653866247109 4198545431817685099921333)
                      ·
                        rfl

theorem cell23_8176638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_8176638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176638 prefixEnd_8176638 := by exact prefixLift 8176638
  have htrace : WordTrace (prefixWord ++ tailWord_8176638) baseStart_8176638 baseEnd_8176638 := by
    simpa [prefixWord, tailWord_8176638, baseEnd_8176638] using wordTrace_append hprefix tailTrace_8176638
  have hstable : (prefixWord ++ tailWord_8176638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176638).length < 2 ^ (prefixWord ++ tailWord_8176638).sum := by decide
  have hdescent : baseEnd_8176638 < baseStart_8176638 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176654 : List Nat := [4, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3]
def baseStart_8176654 : Nat := 118140960795 + 8176654 * 2 ^ 59
def prefixEnd_8176654 : Nat := 4983230072969 + 3 ^ 40 * 8176654 * 2
def baseEnd_8176654 : Nat := 4198553647508157037321259

theorem tailTrace_8176654 : CollatzResearch.WordTrace tailWord_8176654 prefixEnd_8176654 4198553647508157037321259 := by
  unfold tailWord_8176654
  simp only [CollatzResearch.WordTrace]
  refine ⟨37278383964923311771293127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198818047812924329446896677 37278383964923311771293127)
  ·
    refine ⟨55917575947384967656939691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37278383964923311771293127 55917575947384967656939691)
    ·
      refine ⟨83876363921077451485409537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55917575947384967656939691 83876363921077451485409537)
      ·
        refine ⟨62907272940808088614057153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83876363921077451485409537 62907272940808088614057153)
        ·
          refine ⟨47180454705606066460542865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62907272940808088614057153 47180454705606066460542865)
          ·
            refine ⟨35385341029204549845407149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47180454705606066460542865 35385341029204549845407149)
            ·
              refine ⟨13269502885951706192027681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35385341029204549845407149 13269502885951706192027681)
              ·
                refine ⟨9952127164463779644020761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13269502885951706192027681 9952127164463779644020761)
                ·
                  refine ⟨7464095373347834733015571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9952127164463779644020761 7464095373347834733015571)
                  ·
                    refine ⟨11196143060021752099523357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7464095373347834733015571 11196143060021752099523357)
                    ·
                      refine ⟨4198553647508157037321259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11196143060021752099523357 4198553647508157037321259)
                      ·
                        rfl

theorem cell23_8176654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_8176654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176654 prefixEnd_8176654 := by exact prefixLift 8176654
  have htrace : WordTrace (prefixWord ++ tailWord_8176654) baseStart_8176654 baseEnd_8176654 := by
    simpa [prefixWord, tailWord_8176654, baseEnd_8176654] using wordTrace_append hprefix tailTrace_8176654
  have hstable : (prefixWord ++ tailWord_8176654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176654).length < 2 ^ (prefixWord ++ tailWord_8176654).sum := by decide
  have hdescent : baseEnd_8176654 < baseStart_8176654 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176683 : List Nat := [1, 1, 1, 1, 2, 1, 5, 4, 7]
def baseStart_8176683 : Nat := 118140960795 + 8176683 * 2 ^ 59
def prefixEnd_8176683 : Nat := 4983230072969 + 3 ^ 40 * 8176683 * 2
def baseEnd_8176683 : Nat := 466507615383015269317625

theorem tailTrace_8176683 : CollatzResearch.WordTrace tailWord_8176683 prefixEnd_8176683 466507615383015269317625 := by
  unfold tailWord_8176683
  simp only [CollatzResearch.WordTrace]
  refine ⟨298228129436281432123150703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198818752957520954748767135 298228129436281432123150703)
  ·
    refine ⟨447342194154422148184726055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298228129436281432123150703 447342194154422148184726055)
    ·
      refine ⟨671013291231633222277089083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447342194154422148184726055 671013291231633222277089083)
      ·
        refine ⟨1006519936847449833415633625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671013291231633222277089083 1006519936847449833415633625)
        ·
          refine ⟨754889952635587375061725219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1006519936847449833415633625 754889952635587375061725219)
          ·
            refine ⟨1132334928953381062592587829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754889952635587375061725219 1132334928953381062592587829)
            ·
              refine ⟨106156399589379474618055109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1132334928953381062592587829 106156399589379474618055109)
              ·
                refine ⟨19904324923008651490885333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106156399589379474618055109 19904324923008651490885333)
                ·
                  refine ⟨466507615383015269317625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19904324923008651490885333 466507615383015269317625)
                  ·
                    rfl

theorem cell23_8176683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 7].length) (baseStart_8176683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176683 prefixEnd_8176683 := by exact prefixLift 8176683
  have htrace : WordTrace (prefixWord ++ tailWord_8176683) baseStart_8176683 baseEnd_8176683 := by
    simpa [prefixWord, tailWord_8176683, baseEnd_8176683] using wordTrace_append hprefix tailTrace_8176683
  have hstable : (prefixWord ++ tailWord_8176683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176683).length < 2 ^ (prefixWord ++ tailWord_8176683).sum := by decide
  have hdescent : baseEnd_8176683 < baseStart_8176683 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176713 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 3, 7]
def baseStart_8176713 : Nat := 118140960795 + 8176713 * 2 ^ 59
def prefixEnd_8176713 : Nat := 4983230072969 + 3 ^ 40 * 8176713 * 2
def baseEnd_8176713 : Nat := 1399527980955590768827829

theorem tailTrace_8176713 : CollatzResearch.WordTrace tailWord_8176713 prefixEnd_8176713 1399527980955590768827829 := by
  unfold tailWord_8176713
  simp only [CollatzResearch.WordTrace]
  refine ⟨298229223626172747246742793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198819482417448498164495195 298229223626172747246742793)
  ·
    refine ⟨223671917719629560435057095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298229223626172747246742793 223671917719629560435057095)
    ·
      refine ⟨335507876579444340652585643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223671917719629560435057095 335507876579444340652585643)
      ·
        refine ⟨503261814869166510978878465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335507876579444340652585643 503261814869166510978878465)
        ·
          refine ⟨377446361151874883234158849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503261814869166510978878465 377446361151874883234158849)
          ·
            refine ⟨283084770863906162425619137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377446361151874883234158849 283084770863906162425619137)
            ·
              refine ⟨212313578147929621819214353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283084770863906162425619137 212313578147929621819214353)
              ·
                refine ⟨159235183610947216364410765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212313578147929621819214353 159235183610947216364410765)
                ·
                  refine ⟨59713193854105206136654037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159235183610947216364410765 59713193854105206136654037)
                  ·
                    refine ⟨1399527980955590768827829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59713193854105206136654037 1399527980955590768827829)
                    ·
                      rfl

theorem cell23_8176713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 7].length) (baseStart_8176713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176713 prefixEnd_8176713 := by exact prefixLift 8176713
  have htrace : WordTrace (prefixWord ++ tailWord_8176713) baseStart_8176713 baseEnd_8176713 := by
    simpa [prefixWord, tailWord_8176713, baseEnd_8176713] using wordTrace_append hprefix tailTrace_8176713
  have hstable : (prefixWord ++ tailWord_8176713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176713).length < 2 ^ (prefixWord ++ tailWord_8176713).sum := by decide
  have hdescent : baseEnd_8176713 < baseStart_8176713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176717 : List Nat := [1, 6, 1, 1, 1, 2, 3, 1, 7]
def baseStart_8176717 : Nat := 118140960795 + 8176717 * 2 ^ 59
def prefixEnd_8176717 : Nat := 4983230072969 + 3 ^ 40 * 8176717 * 2
def baseEnd_8176717 : Nat := 466509555198821143425941

theorem tailTrace_8176717 : CollatzResearch.WordTrace tailWord_8176717 prefixEnd_8176717 466509555198821143425941 := by
  unfold tailWord_8176717
  simp only [CollatzResearch.WordTrace]
  refine ⟨298229369518158255929888405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198819579678772170619925603 298229369518158255929888405)
  ·
    refine ⟨13979501696163668246713519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 298229369518158255929888405 13979501696163668246713519)
    ·
      refine ⟨20969252544245502370070279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13979501696163668246713519 20969252544245502370070279)
      ·
        refine ⟨31453878816368253555105419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20969252544245502370070279 31453878816368253555105419)
        ·
          refine ⟨47180818224552380332658129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31453878816368253555105419 47180818224552380332658129)
          ·
            refine ⟨35385613668414285249493597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47180818224552380332658129 35385613668414285249493597)
            ·
              refine ⟨13269605125655356968560099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35385613668414285249493597 13269605125655356968560099)
              ·
                refine ⟨19904407688483035452840149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13269605125655356968560099 19904407688483035452840149)
                ·
                  refine ⟨466509555198821143425941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19904407688483035452840149 466509555198821143425941)
                  ·
                    rfl

theorem cell23_8176717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_8176717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176717 prefixEnd_8176717 := by exact prefixLift 8176717
  have htrace : WordTrace (prefixWord ++ tailWord_8176717) baseStart_8176717 baseEnd_8176717 := by
    simpa [prefixWord, tailWord_8176717, baseEnd_8176717] using wordTrace_append hprefix tailTrace_8176717
  have hstable : (prefixWord ++ tailWord_8176717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176717).length < 2 ^ (prefixWord ++ tailWord_8176717).sum := by decide
  have hdescent : baseEnd_8176717 < baseStart_8176717 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176723 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 7]
def baseStart_8176723 : Nat := 118140960795 + 8176723 * 2 ^ 59
def prefixEnd_8176723 : Nat := 4983230072969 + 3 ^ 40 * 8176723 * 2
def baseEnd_8176723 : Nat := 4198589077673317267358441

theorem tailTrace_8176723 : CollatzResearch.WordTrace tailWord_8176723 prefixEnd_8176723 4198589077673317267358441 := by
  unfold tailWord_8176723
  simp only [CollatzResearch.WordTrace]
  refine ⟨298229588356136518954606823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198819725570757679303071215 298229588356136518954606823)
  ·
    refine ⟨447344382534204778431910235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298229588356136518954606823 447344382534204778431910235)
    ·
      refine ⟨671016573801307167647865353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447344382534204778431910235 671016573801307167647865353)
      ·
        refine ⟨503262430350980375735899015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 671016573801307167647865353 503262430350980375735899015)
        ·
          refine ⟨754893645526470563603848523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503262430350980375735899015 754893645526470563603848523)
          ·
            refine ⟨1132340468289705845405772785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754893645526470563603848523 1132340468289705845405772785)
            ·
              refine ⟨849255351217279384054329589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1132340468289705845405772785 849255351217279384054329589)
              ·
                refine ⟨79617689176619942255093399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 849255351217279384054329589 79617689176619942255093399)
                ·
                  refine ⟨119426533764929913382640099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79617689176619942255093399 119426533764929913382640099)
                  ·
                    refine ⟨179139800647394870073960149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119426533764929913382640099 179139800647394870073960149)
                    ·
                      refine ⟨4198589077673317267358441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179139800647394870073960149 4198589077673317267358441)
                      ·
                        rfl

theorem cell23_8176723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_8176723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176723 prefixEnd_8176723 := by exact prefixLift 8176723
  have htrace : WordTrace (prefixWord ++ tailWord_8176723) baseStart_8176723 baseEnd_8176723 := by
    simpa [prefixWord, tailWord_8176723, baseEnd_8176723] using wordTrace_append hprefix tailTrace_8176723
  have hstable : (prefixWord ++ tailWord_8176723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176723).length < 2 ^ (prefixWord ++ tailWord_8176723).sum := by decide
  have hdescent : baseEnd_8176723 < baseStart_8176723 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176794 : List Nat := [3, 1, 1, 5, 1, 2, 1, 2, 3, 4]
def baseStart_8176794 : Nat := 118140960795 + 8176794 * 2 ^ 59
def prefixEnd_8176794 : Nat := 4983230072969 + 3 ^ 40 * 8176794 * 2
def baseEnd_8176794 : Nat := 1399541844933262163190205

theorem tailTrace_8176794 : CollatzResearch.WordTrace tailWord_8176794 prefixEnd_8176794 1399541844933262163190205 := by
  unfold tailWord_8176794
  simp only [CollatzResearch.WordTrace]
  refine ⟨74558044484719824520110359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198821451959252865386960957 74558044484719824520110359)
  ·
    refine ⟨111837066727079736780165539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74558044484719824520110359 111837066727079736780165539)
    ·
      refine ⟨167755600090619605170248309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111837066727079736780165539 167755600090619605170248309)
      ·
        refine ⟨15727087508495587984710779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167755600090619605170248309 15727087508495587984710779)
        ·
          refine ⟨23590631262743381977066169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15727087508495587984710779 23590631262743381977066169)
          ·
            refine ⟨17692973447057536482799627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23590631262743381977066169 17692973447057536482799627)
            ·
              refine ⟨26539460170586304724199441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17692973447057536482799627 26539460170586304724199441)
              ·
                refine ⟨19904595127939728543149581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26539460170586304724199441 19904595127939728543149581)
                ·
                  refine ⟨7464223172977398203681093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19904595127939728543149581 7464223172977398203681093)
                  ·
                    refine ⟨1399541844933262163190205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7464223172977398203681093 1399541844933262163190205)
                    ·
                      rfl

theorem cell23_8176794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 3, 4].length) (baseStart_8176794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176794 prefixEnd_8176794 := by exact prefixLift 8176794
  have htrace : WordTrace (prefixWord ++ tailWord_8176794) baseStart_8176794 baseEnd_8176794 := by
    simpa [prefixWord, tailWord_8176794, baseEnd_8176794] using wordTrace_append hprefix tailTrace_8176794
  have hstable : (prefixWord ++ tailWord_8176794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176794).length < 2 ^ (prefixWord ++ tailWord_8176794).sum := by decide
  have hdescent : baseEnd_8176794 < baseStart_8176794 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176804 : List Nat := [2, 3, 1, 2, 3, 1, 3, 1, 2, 2, 3]
def baseStart_8176804 : Nat := 118140960795 + 8176804 * 2 ^ 59
def prefixEnd_8176804 : Nat := 4983230072969 + 3 ^ 40 * 8176804 * 2
def baseEnd_8176804 : Nat := 4198630669606331450445569

theorem tailTrace_8176804 : CollatzResearch.WordTrace tailWord_8176804 prefixEnd_8176804 4198630669606331450445569 := by
  unfold tailWord_8176804
  simp only [CollatzResearch.WordTrace]
  refine ⟨149116271334421534894152733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198821695112562046525536977 149116271334421534894152733)
  ·
    refine ⟨55918601750408075585307275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149116271334421534894152733 55918601750408075585307275)
    ·
      refine ⟨83877902625612113377960913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55918601750408075585307275 83877902625612113377960913)
      ·
        refine ⟨62908426969209085033470685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83877902625612113377960913 62908426969209085033470685)
        ·
          refine ⟨23590660113453406887551507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62908426969209085033470685 23590660113453406887551507)
          ·
            refine ⟨35385990170180110331327261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23590660113453406887551507 35385990170180110331327261)
            ·
              refine ⟨13269746313817541374247723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35385990170180110331327261 13269746313817541374247723)
              ·
                refine ⟨19904619470726312061371585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13269746313817541374247723 19904619470726312061371585)
                ·
                  refine ⟨14928464603044734046028689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19904619470726312061371585 14928464603044734046028689)
                  ·
                    refine ⟨11196348452283550534521517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14928464603044734046028689 11196348452283550534521517)
                    ·
                      refine ⟨4198630669606331450445569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11196348452283550534521517 4198630669606331450445569)
                      ·
                        rfl

theorem cell23_8176804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_8176804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176804 prefixEnd_8176804 := by exact prefixLift 8176804
  have htrace : WordTrace (prefixWord ++ tailWord_8176804) baseStart_8176804 baseEnd_8176804 := by
    simpa [prefixWord, tailWord_8176804, baseEnd_8176804] using wordTrace_append hprefix tailTrace_8176804
  have hstable : (prefixWord ++ tailWord_8176804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176804).length < 2 ^ (prefixWord ++ tailWord_8176804).sum := by decide
  have hdescent : baseEnd_8176804 < baseStart_8176804 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176857 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 1, 8, 2]
def baseStart_8176857 : Nat := 118140960795 + 8176857 * 2 ^ 59
def prefixEnd_8176857 : Nat := 4983230072969 + 3 ^ 40 * 8176857 * 2
def baseEnd_8176857 : Nat := 4198657884081019743082825

theorem tailTrace_8176857 : CollatzResearch.WordTrace tailWord_8176857 prefixEnd_8176857 4198657884081019743082825 := by
  unfold tailWord_8176857
  simp only [CollatzResearch.WordTrace]
  refine ⟨298234475737651059839984825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198822983825100706559989883 298234475737651059839984825)
  ·
    refine ⟨223675856803238294879988619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298234475737651059839984825 223675856803238294879988619)
    ·
      refine ⟨335513785204857442319982929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223675856803238294879988619 335513785204857442319982929)
      ·
        refine ⟨251635338903643081739987197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335513785204857442319982929 251635338903643081739987197)
        ·
          refine ⟨94363252088866155652495199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251635338903643081739987197 94363252088866155652495199)
          ·
            refine ⟨141544878133299233478742799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94363252088866155652495199 141544878133299233478742799)
            ·
              refine ⟨212317317199948850218114199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141544878133299233478742799 212317317199948850218114199)
              ·
                refine ⟨318475975799923275327171299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212317317199948850218114199 318475975799923275327171299)
                ·
                  refine ⟨477713963699884912990756949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318475975799923275327171299 477713963699884912990756949)
                  ·
                    refine ⟨5598210512108026324110433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 477713963699884912990756949 5598210512108026324110433)
                    ·
                      refine ⟨4198657884081019743082825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5598210512108026324110433 4198657884081019743082825)
                      ·
                        rfl

theorem cell23_8176857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 8, 2].length) (baseStart_8176857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176857 prefixEnd_8176857 := by exact prefixLift 8176857
  have htrace : WordTrace (prefixWord ++ tailWord_8176857) baseStart_8176857 baseEnd_8176857 := by
    simpa [prefixWord, tailWord_8176857, baseEnd_8176857] using wordTrace_append hprefix tailTrace_8176857
  have hstable : (prefixWord ++ tailWord_8176857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176857).length < 2 ^ (prefixWord ++ tailWord_8176857).sum := by decide
  have hdescent : baseEnd_8176857 < baseStart_8176857 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176874 : List Nat := [3, 1, 3, 1, 1, 3, 2, 3, 1, 1, 4]
def baseStart_8176874 : Nat := 118140960795 + 8176874 * 2 ^ 59
def prefixEnd_8176874 : Nat := 4983230072969 + 3 ^ 40 * 8176874 * 2
def baseEnd_8176874 : Nat := 4198666613252146176570247

theorem tailTrace_8176874 : CollatzResearch.WordTrace tailWord_8176874 prefixEnd_8176874 4198666613252146176570247 := by
  unfold tailWord_8176874
  simp only [CollatzResearch.WordTrace]
  refine ⟨74558773944647367935838419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198823397185726314495569117 74558773944647367935838419)
  ·
    refine ⟨111838160916971051903757629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74558773944647367935838419 111838160916971051903757629)
    ·
      refine ⟨41939310343864144463909111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111838160916971051903757629 41939310343864144463909111)
      ·
        refine ⟨62908965515796216695863667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41939310343864144463909111 62908965515796216695863667)
        ·
          refine ⟨94363448273694325043795501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62908965515796216695863667 94363448273694325043795501)
          ·
            refine ⟨35386293102635371891423313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94363448273694325043795501 35386293102635371891423313)
            ·
              refine ⟨26539719826976528918567485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35386293102635371891423313 26539719826976528918567485)
              ·
                refine ⟨9952394935116198344462807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26539719826976528918567485 9952394935116198344462807)
                ·
                  refine ⟨14928592402674297516694211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9952394935116198344462807 14928592402674297516694211)
                  ·
                    refine ⟨22392888604011446275041317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14928592402674297516694211 22392888604011446275041317)
                    ·
                      refine ⟨4198666613252146176570247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22392888604011446275041317 4198666613252146176570247)
                      ·
                        rfl

theorem cell23_8176874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_8176874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176874 prefixEnd_8176874 := by exact prefixLift 8176874
  have htrace : WordTrace (prefixWord ++ tailWord_8176874) baseStart_8176874 baseEnd_8176874 := by
    simpa [prefixWord, tailWord_8176874, baseEnd_8176874] using wordTrace_append hprefix tailTrace_8176874
  have hstable : (prefixWord ++ tailWord_8176874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176874).length < 2 ^ (prefixWord ++ tailWord_8176874).sum := by decide
  have hdescent : baseEnd_8176874 < baseStart_8176874 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176894 : List Nat := [4, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_8176894 : Nat := 118140960795 + 8176894 * 2 ^ 59
def prefixEnd_8176894 : Nat := 4983230072969 + 3 ^ 40 * 8176894 * 2
def baseEnd_8176894 : Nat := 4198676882865236098320155

theorem tailTrace_8176894 : CollatzResearch.WordTrace tailWord_8176894 prefixEnd_8176894 4198676882865236098320155 := by
  unfold tailWord_8176894
  simp only [CollatzResearch.WordTrace]
  refine ⟨37279478154814626894885217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198823883492344676772721157 37279478154814626894885217)
  ·
    refine ⟨27959608616110970171163913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37279478154814626894885217 27959608616110970171163913)
    ·
      refine ⟨20969706462083227628372935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27959608616110970171163913 20969706462083227628372935)
      ·
        refine ⟨31454559693124841442559403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20969706462083227628372935 31454559693124841442559403)
        ·
          refine ⟨47181839539687262163839105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31454559693124841442559403 47181839539687262163839105)
          ·
            refine ⟨35386379654765446622879329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47181839539687262163839105 35386379654765446622879329)
            ·
              refine ⟨26539784741074084967159497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35386379654765446622879329 26539784741074084967159497)
              ·
                refine ⟨19904838555805563725369623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26539784741074084967159497 19904838555805563725369623)
                ·
                  refine ⟨29857257833708345588054435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19904838555805563725369623 29857257833708345588054435)
                  ·
                    refine ⟨44785886750562518382081653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29857257833708345588054435 44785886750562518382081653)
                    ·
                      refine ⟨4198676882865236098320155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44785886750562518382081653 4198676882865236098320155)
                      ·
                        rfl

theorem cell23_8176894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_8176894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176894 prefixEnd_8176894 := by exact prefixLift 8176894
  have htrace : WordTrace (prefixWord ++ tailWord_8176894) baseStart_8176894 baseEnd_8176894 := by
    simpa [prefixWord, tailWord_8176894, baseEnd_8176894] using wordTrace_append hprefix tailTrace_8176894
  have hstable : (prefixWord ++ tailWord_8176894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176894).length < 2 ^ (prefixWord ++ tailWord_8176894).sum := by decide
  have hdescent : baseEnd_8176894 < baseStart_8176894 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176897 : List Nat := [1, 2, 4, 1, 1, 4, 2, 8]
def baseStart_8176897 : Nat := 118140960795 + 8176897 * 2 ^ 59
def prefixEnd_8176897 : Nat := 4983230072969 + 3 ^ 40 * 8176897 * 2
def baseEnd_8176897 : Nat := 155506608270637021725283

theorem tailTrace_8176897 : CollatzResearch.WordTrace tailWord_8176897 prefixEnd_8176897 155506608270637021725283 := by
  unfold tailWord_8176897
  simp only [CollatzResearch.WordTrace]
  refine ⟨298235934657506146671440945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198823956438337431114293963 298235934657506146671440945)
  ·
    refine ⟨223676950993129610003580709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298235934657506146671440945 223676950993129610003580709)
    ·
      refine ⟨41939428311211801875671383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223676950993129610003580709 41939428311211801875671383)
      ·
        refine ⟨62909142466817702813507075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41939428311211801875671383 62909142466817702813507075)
        ·
          refine ⟨94363713700226554220260613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62909142466817702813507075 94363713700226554220260613)
          ·
            refine ⟨17693196318792478916298865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94363713700226554220260613 17693196318792478916298865)
            ·
              refine ⟨13269897239094359187224149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17693196318792478916298865 13269897239094359187224149)
              ·
                refine ⟨155506608270637021725283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13269897239094359187224149 155506608270637021725283)
                ·
                  rfl

theorem cell23_8176897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 8].length) (baseStart_8176897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176897 prefixEnd_8176897 := by exact prefixLift 8176897
  have htrace : WordTrace (prefixWord ++ tailWord_8176897) baseStart_8176897 baseEnd_8176897 := by
    simpa [prefixWord, tailWord_8176897, baseEnd_8176897] using wordTrace_append hprefix tailTrace_8176897
  have hstable : (prefixWord ++ tailWord_8176897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176897).length < 2 ^ (prefixWord ++ tailWord_8176897).sum := by decide
  have hdescent : baseEnd_8176897 < baseStart_8176897 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176924 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 6, 1, 3]
def baseStart_8176924 : Nat := 118140960795 + 8176924 * 2 ^ 59
def prefixEnd_8176924 : Nat := 4983230072969 + 3 ^ 40 * 8176924 * 2
def baseEnd_8176924 : Nat := 4198692287284870980945017

theorem tailTrace_8176924 : CollatzResearch.WordTrace tailWord_8176924 prefixEnd_8176924 4198692287284870980945017 := by
  unfold tailWord_8176924
  simp only [CollatzResearch.WordTrace]
  refine ⟨149118459714204165141336913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198824612952272220188449217 149118459714204165141336913)
  ·
    refine ⟨111838844785653123856002685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149118459714204165141336913 111838844785653123856002685)
    ·
      refine ⟨41939566794619921446001007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111838844785653123856002685 41939566794619921446001007)
      ·
        refine ⟨62909350191929882169001511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41939566794619921446001007 62909350191929882169001511)
        ·
          refine ⟨94364025287894823253502267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62909350191929882169001511 94364025287894823253502267)
          ·
            refine ⟨141546037931842234880253401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94364025287894823253502267 141546037931842234880253401)
            ·
              refine ⟨106159528448881676160190051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141546037931842234880253401 106159528448881676160190051)
              ·
                refine ⟨159239292673322514240285077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106159528448881676160190051 159239292673322514240285077)
                ·
                  refine ⟨7464341844061992855013363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159239292673322514240285077 7464341844061992855013363)
                  ·
                    refine ⟨11196512766092989282520045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7464341844061992855013363 11196512766092989282520045)
                    ·
                      refine ⟨4198692287284870980945017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11196512766092989282520045 4198692287284870980945017)
                      ·
                        rfl

theorem cell23_8176924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_8176924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176924 prefixEnd_8176924 := by exact prefixLift 8176924
  have htrace : WordTrace (prefixWord ++ tailWord_8176924) baseStart_8176924 baseEnd_8176924 := by
    simpa [prefixWord, tailWord_8176924, baseEnd_8176924] using wordTrace_append hprefix tailTrace_8176924
  have hstable : (prefixWord ++ tailWord_8176924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176924).length < 2 ^ (prefixWord ++ tailWord_8176924).sum := by decide
  have hdescent : baseEnd_8176924 < baseStart_8176924 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176928 : List Nat := [2, 1, 1, 5, 3, 1, 3, 1, 1, 2, 3]
def baseStart_8176928 : Nat := 118140960795 + 8176928 * 2 ^ 59
def prefixEnd_8176928 : Nat := 4983230072969 + 3 ^ 40 * 8176928 * 2
def baseEnd_8176928 : Nat := 4198694341207488965294999

theorem tailTrace_8176928 : CollatzResearch.WordTrace tailWord_8176928 prefixEnd_8176928 4198694341207488965294999 := by
  unfold tailWord_8176928
  simp only [CollatzResearch.WordTrace]
  refine ⟨149118532660196919482909719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198824710213595892643879625 149118532660196919482909719)
  ·
    refine ⟨223677798990295379224364579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149118532660196919482909719 223677798990295379224364579)
    ·
      refine ⟨335516698485443068836546869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223677798990295379224364579 335516698485443068836546869)
      ·
        refine ⟨31454690483010287703426269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 335516698485443068836546869 31454690483010287703426269)
        ·
          refine ⟨11795508931128857888784851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31454690483010287703426269 11795508931128857888784851)
          ·
            refine ⟨17693263396693286833177277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11795508931128857888784851 17693263396693286833177277)
            ·
              refine ⟨6634973773759982562441479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17693263396693286833177277 6634973773759982562441479)
              ·
                refine ⟨9952460660639973843662219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6634973773759982562441479 9952460660639973843662219)
                ·
                  refine ⟨14928690990959960765493329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9952460660639973843662219 14928690990959960765493329)
                  ·
                    refine ⟨11196518243219970574119997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14928690990959960765493329 11196518243219970574119997)
                    ·
                      refine ⟨4198694341207488965294999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11196518243219970574119997 4198694341207488965294999)
                      ·
                        rfl

theorem cell23_8176928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_8176928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176928 prefixEnd_8176928 := by exact prefixLift 8176928
  have htrace : WordTrace (prefixWord ++ tailWord_8176928) baseStart_8176928 baseEnd_8176928 := by
    simpa [prefixWord, tailWord_8176928, baseEnd_8176928] using wordTrace_append hprefix tailTrace_8176928
  have hstable : (prefixWord ++ tailWord_8176928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176928).length < 2 ^ (prefixWord ++ tailWord_8176928).sum := by decide
  have hdescent : baseEnd_8176928 < baseStart_8176928 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176947 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 4]
def baseStart_8176947 : Nat := 118140960795 + 8176947 * 2 ^ 59
def prefixEnd_8176947 : Nat := 4983230072969 + 3 ^ 40 * 8176947 * 2
def baseEnd_8176947 : Nat := 4198704097339924390957411

theorem tailTrace_8176947 : CollatzResearch.WordTrace tailWord_8176947 prefixEnd_8176947 4198704097339924390957411 := by
  unfold tailWord_8176947
  simp only [CollatzResearch.WordTrace]
  refine ⟨298237758307325005210761095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198825172204883336807174063 298237758307325005210761095)
  ·
    refine ⟨447356637460987507816141643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298237758307325005210761095 447356637460987507816141643)
    ·
      refine ⟨671034956191481261724212465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447356637460987507816141643 671034956191481261724212465)
      ·
        refine ⟨503276217143610946293159349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 671034956191481261724212465 503276217143610946293159349)
        ·
          refine ⟨47182145357213526214983689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 503276217143610946293159349 47182145357213526214983689)
          ·
            refine ⟨35386609017910144661237767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47182145357213526214983689 35386609017910144661237767)
            ·
              refine ⟨53079913526865216991856651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35386609017910144661237767 53079913526865216991856651)
              ·
                refine ⟨79619870290297825487784977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53079913526865216991856651 79619870290297825487784977)
                ·
                  refine ⟨59714902717723369115838733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79619870290297825487784977 59714902717723369115838733)
                  ·
                    refine ⟨22393088519146263418439525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59714902717723369115838733 22393088519146263418439525)
                    ·
                      refine ⟨4198704097339924390957411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22393088519146263418439525 4198704097339924390957411)
                      ·
                        rfl

theorem cell23_8176947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 4].length) (baseStart_8176947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176947 prefixEnd_8176947 := by exact prefixLift 8176947
  have htrace : WordTrace (prefixWord ++ tailWord_8176947) baseStart_8176947 baseEnd_8176947 := by
    simpa [prefixWord, tailWord_8176947, baseEnd_8176947] using wordTrace_append hprefix tailTrace_8176947
  have hstable : (prefixWord ++ tailWord_8176947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176947).length < 2 ^ (prefixWord ++ tailWord_8176947).sum := by decide
  have hdescent : baseEnd_8176947 < baseStart_8176947 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176977 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 1, 4, 4]
def baseStart_8176977 : Nat := 118140960795 + 8176977 * 2 ^ 59
def prefixEnd_8176977 : Nat := 4983230072969 + 3 ^ 40 * 8176977 * 2
def baseEnd_8176977 : Nat := 4198719501759559273582273

theorem tailTrace_8176977 : CollatzResearch.WordTrace tailWord_8176977 prefixEnd_8176977 4198719501759559273582273 := by
  unfold tailWord_8176977
  simp only [CollatzResearch.WordTrace]
  refine ⟨298238852497216320334353185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198825901664810880222902123 298238852497216320334353185)
  ·
    refine ⟨223679139372912240250764889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298238852497216320334353185 223679139372912240250764889)
    ·
      refine ⟨167759354529684180188073667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223679139372912240250764889 167759354529684180188073667)
      ·
        refine ⟨251639031794526270282110501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167759354529684180188073667 251639031794526270282110501)
        ·
          refine ⟨47182318461473675677895719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251639031794526270282110501 47182318461473675677895719)
          ·
            refine ⟨70773477692210513516843579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47182318461473675677895719 70773477692210513516843579)
            ·
              refine ⟨106160216538315770275265369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70773477692210513516843579 106160216538315770275265369)
              ·
                refine ⟨79620162403736827706449027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106160216538315770275265369 79620162403736827706449027)
                ·
                  refine ⟨119430243605605241559673541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79620162403736827706449027 119430243605605241559673541)
                  ·
                    refine ⟨22393170676050982792438789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119430243605605241559673541 22393170676050982792438789)
                    ·
                      refine ⟨4198719501759559273582273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22393170676050982792438789 4198719501759559273582273)
                      ·
                        rfl

theorem cell23_8176977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_8176977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176977 prefixEnd_8176977 := by exact prefixLift 8176977
  have htrace : WordTrace (prefixWord ++ tailWord_8176977) baseStart_8176977 baseEnd_8176977 := by
    simpa [prefixWord, tailWord_8176977, baseEnd_8176977] using wordTrace_append hprefix tailTrace_8176977
  have hstable : (prefixWord ++ tailWord_8176977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176977).length < 2 ^ (prefixWord ++ tailWord_8176977).sum := by decide
  have hdescent : baseEnd_8176977 < baseStart_8176977 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176981 : List Nat := [1, 3, 2, 2, 3, 1, 2, 2, 1, 4, 2]
def baseStart_8176981 : Nat := 118140960795 + 8176981 * 2 ^ 59
def prefixEnd_8176981 : Nat := 4983230072969 + 3 ^ 40 * 8176981 * 2
def baseEnd_8176981 : Nat := 4198721555682177257932255

theorem tailTrace_8176981 : CollatzResearch.WordTrace tailWord_8176981 prefixEnd_8176981 4198721555682177257932255 := by
  unfold tailWord_8176981
  simp only [CollatzResearch.WordTrace]
  refine ⟨298238998389201829017498797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198825998926134552678332531 298238998389201829017498797)
  ·
    refine ⟨111839624395950685881562049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298238998389201829017498797 111839624395950685881562049)
    ·
      refine ⟨83879718296963014411171537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111839624395950685881562049 83879718296963014411171537)
      ·
        refine ⟨62909788722722260808378653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83879718296963014411171537 62909788722722260808378653)
        ·
          refine ⟨23591170771020847803141995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62909788722722260808378653 23591170771020847803141995)
          ·
            refine ⟨35386756156531271704712993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23591170771020847803141995 35386756156531271704712993)
            ·
              refine ⟨26540067117398453778534745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35386756156531271704712993 26540067117398453778534745)
              ·
                refine ⟨19905050338048840333901059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26540067117398453778534745 19905050338048840333901059)
                ·
                  refine ⟨29857575507073260500851589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19905050338048840333901059 29857575507073260500851589)
                  ·
                    refine ⟨5598295407576236343909673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29857575507073260500851589 5598295407576236343909673)
                    ·
                      refine ⟨4198721555682177257932255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5598295407576236343909673 4198721555682177257932255)
                      ·
                        rfl

theorem cell23_8176981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_8176981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176981 prefixEnd_8176981 := by exact prefixLift 8176981
  have htrace : WordTrace (prefixWord ++ tailWord_8176981) baseStart_8176981 baseEnd_8176981 := by
    simpa [prefixWord, tailWord_8176981, baseEnd_8176981] using wordTrace_append hprefix tailTrace_8176981
  have hstable : (prefixWord ++ tailWord_8176981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176981).length < 2 ^ (prefixWord ++ tailWord_8176981).sum := by decide
  have hdescent : baseEnd_8176981 < baseStart_8176981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8176994 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_8176994 : Nat := 118140960795 + 8176994 * 2 ^ 59
def prefixEnd_8176994 : Nat := 4983230072969 + 3 ^ 40 * 8176994 * 2
def baseEnd_8176994 : Nat := 4198728230930685707069695

theorem tailTrace_8176994 : CollatzResearch.WordTrace tailWord_8176994 prefixEnd_8176994 4198728230930685707069695 := by
  unfold tailWord_8176994
  simp only [CollatzResearch.WordTrace]
  refine ⟨74559868134538683059430509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198826315025436488158481357 74559868134538683059430509)
  ·
    refine ⟨27959950550452006147286441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74559868134538683059430509 27959950550452006147286441)
    ·
      refine ⟨20969962912839004610464831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27959950550452006147286441 20969962912839004610464831)
      ·
        refine ⟨31454944369258506915697247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20969962912839004610464831 31454944369258506915697247)
        ·
          refine ⟨47182416553887760373545871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31454944369258506915697247 47182416553887760373545871)
          ·
            refine ⟨70773624830831640560318807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47182416553887760373545871 70773624830831640560318807)
            ·
              refine ⟨106160437246247460840478211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70773624830831640560318807 106160437246247460840478211)
              ·
                refine ⟨159240655869371191260717317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106160437246247460840478211 159240655869371191260717317)
                ·
                  refine ⟨29857622975507098361384497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159240655869371191260717317 29857622975507098361384497)
                  ·
                    refine ⟨22393217231630323771038373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29857622975507098361384497 22393217231630323771038373)
                    ·
                      refine ⟨4198728230930685707069695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22393217231630323771038373 4198728230930685707069695)
                      ·
                        rfl

theorem cell23_8176994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_8176994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8176994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8176994 prefixEnd_8176994 := by exact prefixLift 8176994
  have htrace : WordTrace (prefixWord ++ tailWord_8176994) baseStart_8176994 baseEnd_8176994 := by
    simpa [prefixWord, tailWord_8176994, baseEnd_8176994] using wordTrace_append hprefix tailTrace_8176994
  have hstable : (prefixWord ++ tailWord_8176994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8176994).length < 2 ^ (prefixWord ++ tailWord_8176994).sum := by decide
  have hdescent : baseEnd_8176994 < baseStart_8176994 := by decide
  rcases family_descends (prefixWord ++ tailWord_8176994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177004 : List Nat := [2, 2, 1, 1, 5, 2, 2, 1, 7]
def baseStart_8177004 : Nat := 118140960795 + 8177004 * 2 ^ 59
def prefixEnd_8177004 : Nat := 4983230072969 + 3 ^ 40 * 8177004 * 2
def baseEnd_8177004 : Nat := 466525929526358963104961

theorem tailTrace_8177004 : CollatzResearch.WordTrace tailWord_8177004 prefixEnd_8177004 466525929526358963104961 := by
  unfold tailWord_8177004
  simp only [CollatzResearch.WordTrace]
  refine ⟨149119918634059251972793033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198826558178745669297057377 149119918634059251972793033)
  ·
    refine ⟨111839938975544438979594775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149119918634059251972793033 111839938975544438979594775)
    ·
      refine ⟨167759908463316658469392163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111839938975544438979594775 167759908463316658469392163)
      ·
        refine ⟨251639862694974987704088245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167759908463316658469392163 251639862694974987704088245)
        ·
          refine ⟨23591237127653905097258273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 251639862694974987704088245 23591237127653905097258273)
          ·
            refine ⟨17693427845740428822943705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23591237127653905097258273 17693427845740428822943705)
            ·
              refine ⟨13270070884305321617207779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17693427845740428822943705 13270070884305321617207779)
              ·
                refine ⟨19905106326457982425811669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13270070884305321617207779 19905106326457982425811669)
                ·
                  refine ⟨466525929526358963104961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19905106326457982425811669 466525929526358963104961)
                  ·
                    rfl

theorem cell23_8177004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 7].length) (baseStart_8177004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177004 prefixEnd_8177004 := by exact prefixLift 8177004
  have htrace : WordTrace (prefixWord ++ tailWord_8177004) baseStart_8177004 baseEnd_8177004 := by
    simpa [prefixWord, tailWord_8177004, baseEnd_8177004] using wordTrace_append hprefix tailTrace_8177004
  have hstable : (prefixWord ++ tailWord_8177004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177004).length < 2 ^ (prefixWord ++ tailWord_8177004).sum := by decide
  have hdescent : baseEnd_8177004 < baseStart_8177004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177017 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 1, 7]
def baseStart_8177017 : Nat := 118140960795 + 8177017 * 2 ^ 59
def prefixEnd_8177017 : Nat := 4983230072969 + 3 ^ 40 * 8177017 * 2
def baseEnd_8177017 : Nat := 1399580013661913039027363

theorem tailTrace_8177017 : CollatzResearch.WordTrace tailWord_8177017 prefixEnd_8177017 1399580013661913039027363 := by
  unfold tailWord_8177017
  simp only [CollatzResearch.WordTrace]
  refine ⟨298240311417071407165809305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198826874278047604777206203 298240311417071407165809305)
  ·
    refine ⟨223680233562803555374356979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298240311417071407165809305 223680233562803555374356979)
    ·
      refine ⟨335520350344205333061535469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223680233562803555374356979 335520350344205333061535469)
      ·
        refine ⟨125820131379076999898075801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335520350344205333061535469 125820131379076999898075801)
        ·
          refine ⟨94365098534307749923556851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125820131379076999898075801 94365098534307749923556851)
          ·
            refine ⟨141547647801461624885335277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94365098534307749923556851 141547647801461624885335277)
            ·
              refine ⟨53080367925548109332000729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141547647801461624885335277 53080367925548109332000729)
              ·
                refine ⟨39810275944161081999000547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53080367925548109332000729 39810275944161081999000547)
                ·
                  refine ⟨59715413916241622998500821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39810275944161081999000547 59715413916241622998500821)
                  ·
                    refine ⟨1399580013661913039027363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59715413916241622998500821 1399580013661913039027363)
                    ·
                      rfl

theorem cell23_8177017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 7].length) (baseStart_8177017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177017 prefixEnd_8177017 := by exact prefixLift 8177017
  have htrace : WordTrace (prefixWord ++ tailWord_8177017) baseStart_8177017 baseEnd_8177017 := by
    simpa [prefixWord, tailWord_8177017, baseEnd_8177017] using wordTrace_append hprefix tailTrace_8177017
  have hstable : (prefixWord ++ tailWord_8177017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177017).length < 2 ^ (prefixWord ++ tailWord_8177017).sum := by decide
  have hdescent : baseEnd_8177017 < baseStart_8177017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177024 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 2, 5, 2]
def baseStart_8177024 : Nat := 118140960795 + 8177024 * 2 ^ 59
def prefixEnd_8177024 : Nat := 4983230072969 + 3 ^ 40 * 8177024 * 2
def baseEnd_8177024 : Nat := 4198743635350320589694557

theorem tailTrace_8177024 : CollatzResearch.WordTrace tailWord_8177024 prefixEnd_8177024 4198743635350320589694557 := by
  unfold tailWord_8177024
  simp only [CollatzResearch.WordTrace]
  refine ⟨149120283364023023680657063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198827044485364031574209417 149120283364023023680657063)
  ·
    refine ⟨223680425046034535520985595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149120283364023023680657063 223680425046034535520985595)
    ·
      refine ⟨335520637569051803281478393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223680425046034535520985595 335520637569051803281478393)
      ·
        refine ⟨251640478176788852461108795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335520637569051803281478393 251640478176788852461108795)
        ·
          refine ⟨377460717265183278691663193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251640478176788852461108795 377460717265183278691663193)
          ·
            refine ⟨283095537948887459018747395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377460717265183278691663193 283095537948887459018747395)
            ·
              refine ⟨424643306923331188528121093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283095537948887459018747395 424643306923331188528121093)
              ·
                refine ⟨79620620048124597849022705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 424643306923331188528121093 79620620048124597849022705)
                ·
                  refine ⟨59715465036093448386767029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79620620048124597849022705 59715465036093448386767029)
                  ·
                    refine ⟨5598324847133760786259409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59715465036093448386767029 5598324847133760786259409)
                    ·
                      refine ⟨4198743635350320589694557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5598324847133760786259409 4198743635350320589694557)
                      ·
                        rfl

theorem cell23_8177024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 5, 2].length) (baseStart_8177024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177024 prefixEnd_8177024 := by exact prefixLift 8177024
  have htrace : WordTrace (prefixWord ++ tailWord_8177024) baseStart_8177024 baseEnd_8177024 := by
    simpa [prefixWord, tailWord_8177024, baseEnd_8177024] using wordTrace_append hprefix tailTrace_8177024
  have hstable : (prefixWord ++ tailWord_8177024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177024).length < 2 ^ (prefixWord ++ tailWord_8177024).sum := by decide
  have hdescent : baseEnd_8177024 < baseStart_8177024 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177067 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 4]
def baseStart_8177067 : Nat := 118140960795 + 8177067 * 2 ^ 59
def prefixEnd_8177067 : Nat := 4983230072969 + 3 ^ 40 * 8177067 * 2
def baseEnd_8177067 : Nat := 4198765715018463921456859

theorem tailTrace_8177067 : CollatzResearch.WordTrace tailWord_8177067 prefixEnd_8177067 4198765715018463921456859 := by
  unfold tailWord_8177067
  simp only [CollatzResearch.WordTrace]
  refine ⟨298242135066890265705129455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198828090044593510470086303 298242135066890265705129455)
  ·
    refine ⟨447363202600335398557694183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298242135066890265705129455 447363202600335398557694183)
    ·
      refine ⟨671044803900503097836541275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447363202600335398557694183 671044803900503097836541275)
      ·
        refine ⟨1006567205850754646754811913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671044803900503097836541275 1006567205850754646754811913)
        ·
          refine ⟨754925404388065985066108935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1006567205850754646754811913 754925404388065985066108935)
          ·
            refine ⟨1132388106582098977599163403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754925404388065985066108935 1132388106582098977599163403)
            ·
              refine ⟨1698582159873148466398745105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132388106582098977599163403 1698582159873148466398745105)
              ·
                refine ⟨1273936619904861349799058829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1698582159873148466398745105 1273936619904861349799058829)
                ·
                  refine ⟨477726232464323006174647061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1273936619904861349799058829 477726232464323006174647061)
                  ·
                    refine ⟨22393417146765140914436581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 477726232464323006174647061 22393417146765140914436581)
                    ·
                      refine ⟨4198765715018463921456859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22393417146765140914436581 4198765715018463921456859)
                      ·
                        rfl

theorem cell23_8177067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 4].length) (baseStart_8177067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177067 prefixEnd_8177067 := by exact prefixLift 8177067
  have htrace : WordTrace (prefixWord ++ tailWord_8177067) baseStart_8177067 baseEnd_8177067 := by
    simpa [prefixWord, tailWord_8177067, baseEnd_8177067] using wordTrace_append hprefix tailTrace_8177067
  have hstable : (prefixWord ++ tailWord_8177067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177067).length < 2 ^ (prefixWord ++ tailWord_8177067).sum := by decide
  have hdescent : baseEnd_8177067 < baseStart_8177067 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177074 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3]
def baseStart_8177074 : Nat := 118140960795 + 8177074 * 2 ^ 59
def prefixEnd_8177074 : Nat := 4983230072969 + 3 ^ 40 * 8177074 * 2
def baseEnd_8177074 : Nat := 4198769309383045394069327

theorem tailTrace_8177074 : CollatzResearch.WordTrace tailWord_8177074 prefixEnd_8177074 4198769309383045394069327 := by
  unfold tailWord_8177074
  simp only [CollatzResearch.WordTrace]
  refine ⟨74560597594466226475158569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198828260251909937267089517 74560597594466226475158569)
  ·
    refine ⟨55920448195849669856368927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74560597594466226475158569 55920448195849669856368927)
    ·
      refine ⟨83880672293774504784553391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55920448195849669856368927 83880672293774504784553391)
      ·
        refine ⟨125821008440661757176830087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83880672293774504784553391 125821008440661757176830087)
        ·
          refine ⟨188731512660992635765245131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125821008440661757176830087 188731512660992635765245131)
          ·
            refine ⟨283097268991488953647867697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188731512660992635765245131 283097268991488953647867697)
            ·
              refine ⟨212322951743616715235900773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283097268991488953647867697 212322951743616715235900773)
              ·
                refine ⟨39810553451928134106731395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212322951743616715235900773 39810553451928134106731395)
                ·
                  refine ⟨59715830177892201160097093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39810553451928134106731395 59715830177892201160097093)
                  ·
                    refine ⟨11196718158354787717518205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59715830177892201160097093 11196718158354787717518205)
                    ·
                      refine ⟨4198769309383045394069327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11196718158354787717518205 4198769309383045394069327)
                      ·
                        rfl

theorem cell23_8177074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_8177074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177074 prefixEnd_8177074 := by exact prefixLift 8177074
  have htrace : WordTrace (prefixWord ++ tailWord_8177074) baseStart_8177074 baseEnd_8177074 := by
    simpa [prefixWord, tailWord_8177074, baseEnd_8177074] using wordTrace_append hprefix tailTrace_8177074
  have hstable : (prefixWord ++ tailWord_8177074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177074).length < 2 ^ (prefixWord ++ tailWord_8177074).sum := by decide
  have hdescent : baseEnd_8177074 < baseStart_8177074 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177097 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 8]
def baseStart_8177097 : Nat := 118140960795 + 8177097 * 2 ^ 59
def prefixEnd_8177097 : Nat := 4983230072969 + 3 ^ 40 * 8177097 * 2
def baseEnd_8177097 : Nat := 4198781119438098804081721

theorem tailTrace_8177097 : CollatzResearch.WordTrace tailWord_8177097 prefixEnd_8177097 4198781119438098804081721 := by
  unfold tailWord_8177097
  simp only [CollatzResearch.WordTrace]
  refine ⟨298243229256781580828721545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198828819504521053885814363 298243229256781580828721545)
  ·
    refine ⟨223682421942586185621541159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298243229256781580828721545 223682421942586185621541159)
    ·
      refine ⟨335523632913879278432311739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223682421942586185621541159 335523632913879278432311739)
      ·
        refine ⟨503285449370818917648467609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335523632913879278432311739 503285449370818917648467609)
        ·
          refine ⟨377464087028114188236350707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503285449370818917648467609 377464087028114188236350707)
          ·
            refine ⟨566196130542171282354526061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377464087028114188236350707 566196130542171282354526061)
            ·
              refine ⟨212323548953314230882947273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 566196130542171282354526061 212323548953314230882947273)
              ·
                refine ⟨159242661714985673162210455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212323548953314230882947273 159242661714985673162210455)
                ·
                  refine ⟨238863992572478509743315683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159242661714985673162210455 238863992572478509743315683)
                  ·
                    refine ⟨358295988858717764614973525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 238863992572478509743315683 358295988858717764614973525)
                    ·
                      refine ⟨4198781119438098804081721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 358295988858717764614973525 4198781119438098804081721)
                      ·
                        rfl

theorem cell23_8177097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_8177097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177097 prefixEnd_8177097 := by exact prefixLift 8177097
  have htrace : WordTrace (prefixWord ++ tailWord_8177097) baseStart_8177097 baseEnd_8177097 := by
    simpa [prefixWord, tailWord_8177097, baseEnd_8177097] using wordTrace_append hprefix tailTrace_8177097
  have hstable : (prefixWord ++ tailWord_8177097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177097).length < 2 ^ (prefixWord ++ tailWord_8177097).sum := by decide
  have hdescent : baseEnd_8177097 < baseStart_8177097 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177134 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_8177134 : Nat := 118140960795 + 8177134 * 2 ^ 59
def prefixEnd_8177134 : Nat := 4983230072969 + 3 ^ 40 * 8177134 * 2
def baseEnd_8177134 : Nat := 4198800118222315159319051

theorem tailTrace_8177134 : CollatzResearch.WordTrace tailWord_8177134 prefixEnd_8177134 4198800118222315159319051 := by
  unfold tailWord_8177134
  simp only [CollatzResearch.WordTrace]
  refine ⟨37280572344705942018477307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198829719171765024098545637 37280572344705942018477307)
  ·
    refine ⟨55920858517058913027715961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37280572344705942018477307 55920858517058913027715961)
    ·
      refine ⟨41940643887794184770786971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55920858517058913027715961 41940643887794184770786971)
      ·
        refine ⟨62910965831691277156180457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41940643887794184770786971 62910965831691277156180457)
        ·
          refine ⟨47183224373768457867135343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62910965831691277156180457 47183224373768457867135343)
          ·
            refine ⟨70774836560652686800703015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47183224373768457867135343 70774836560652686800703015)
            ·
              refine ⟨106162254840979030201054523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70774836560652686800703015 106162254840979030201054523)
              ·
                refine ⟨159243382261468545301581785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106162254840979030201054523 159243382261468545301581785)
                ·
                  refine ⟨119432536696101408976186339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159243382261468545301581785 119432536696101408976186339)
                  ·
                    refine ⟨179148805044152113464279509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119432536696101408976186339 179148805044152113464279509)
                    ·
                      refine ⟨4198800118222315159319051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179148805044152113464279509 4198800118222315159319051)
                      ·
                        rfl

theorem cell23_8177134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_8177134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177134 prefixEnd_8177134 := by exact prefixLift 8177134
  have htrace : WordTrace (prefixWord ++ tailWord_8177134) baseStart_8177134 baseEnd_8177134 := by
    simpa [prefixWord, tailWord_8177134, baseEnd_8177134] using wordTrace_append hprefix tailTrace_8177134
  have hstable : (prefixWord ++ tailWord_8177134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177134).length < 2 ^ (prefixWord ++ tailWord_8177134).sum := by decide
  have hdescent : baseEnd_8177134 < baseStart_8177134 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177138 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 5, 1, 3]
def baseStart_8177138 : Nat := 118140960795 + 8177138 * 2 ^ 59
def prefixEnd_8177138 : Nat := 4983230072969 + 3 ^ 40 * 8177138 * 2
def baseEnd_8177138 : Nat := 4198802172144933143669033

theorem tailTrace_8177138 : CollatzResearch.WordTrace tailWord_8177138 prefixEnd_8177138 4198802172144933143669033 := by
  unfold tailWord_8177138
  simp only [CollatzResearch.WordTrace]
  refine ⟨74561181162408261207741017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198829816433088696553976045 74561181162408261207741017)
  ·
    refine ⟨55920885871806195905805763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74561181162408261207741017 55920885871806195905805763)
    ·
      refine ⟨83881328807709293858708645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55920885871806195905805763 83881328807709293858708645)
      ·
        refine ⟨15727749151445492598507871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83881328807709293858708645 15727749151445492598507871)
        ·
          refine ⟨23591623727168238897761807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15727749151445492598507871 23591623727168238897761807)
          ·
            refine ⟨35387435590752358346642711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23591623727168238897761807 35387435590752358346642711)
            ·
              refine ⟨53081153386128537519964067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35387435590752358346642711 53081153386128537519964067)
              ·
                refine ⟨79621730079192806279946101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53081153386128537519964067 79621730079192806279946101)
                ·
                  refine ⟨7464537194924325588744947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79621730079192806279946101 7464537194924325588744947)
                  ·
                    refine ⟨11196805792386488383117421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7464537194924325588744947 11196805792386488383117421)
                    ·
                      refine ⟨4198802172144933143669033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11196805792386488383117421 4198802172144933143669033)
                      ·
                        rfl

theorem cell23_8177138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_8177138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177138 prefixEnd_8177138 := by exact prefixLift 8177138
  have htrace : WordTrace (prefixWord ++ tailWord_8177138) baseStart_8177138 baseEnd_8177138 := by
    simpa [prefixWord, tailWord_8177138, baseEnd_8177138] using wordTrace_append hprefix tailTrace_8177138
  have hstable : (prefixWord ++ tailWord_8177138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177138).length < 2 ^ (prefixWord ++ tailWord_8177138).sum := by decide
  have hdescent : baseEnd_8177138 < baseStart_8177138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177148 : List Nat := [2, 2, 2, 1, 2, 1, 5, 1, 2, 3, 2]
def baseStart_8177148 : Nat := 118140960795 + 8177148 * 2 ^ 59
def prefixEnd_8177148 : Nat := 4983230072969 + 3 ^ 40 * 8177148 * 2
def baseEnd_8177148 : Nat := 4198807306951478104543987

theorem tailTrace_8177148 : CollatzResearch.WordTrace tailWord_8177148 prefixEnd_8177148 4198807306951478104543987 := by
  unfold tailWord_8177148
  simp only [CollatzResearch.WordTrace]
  refine ⟨149122544689798408269414049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198830059586397877692552065 149122544689798408269414049)
  ·
    refine ⟨111841908517348806202060537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149122544689798408269414049 111841908517348806202060537)
    ·
      refine ⟨83881431388011604651545403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111841908517348806202060537 83881431388011604651545403)
      ·
        refine ⟨125822147082017406977318105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83881431388011604651545403 125822147082017406977318105)
        ·
          refine ⟨94366610311513055232988579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125822147082017406977318105 94366610311513055232988579)
          ·
            refine ⟨141549915467269582849482869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94366610311513055232988579 141549915467269582849482869)
            ·
              refine ⟨13270304575056523392139019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141549915467269582849482869 13270304575056523392139019)
              ·
                refine ⟨19905456862584785088208529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13270304575056523392139019 19905456862584785088208529)
                ·
                  refine ⟨14929092646938588816156397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19905456862584785088208529 14929092646938588816156397)
                  ·
                    refine ⟨5598409742601970806058649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14929092646938588816156397 5598409742601970806058649)
                    ·
                      refine ⟨4198807306951478104543987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5598409742601970806058649 4198807306951478104543987)
                      ·
                        rfl

theorem cell23_8177148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_8177148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177148 prefixEnd_8177148 := by exact prefixLift 8177148
  have htrace : WordTrace (prefixWord ++ tailWord_8177148) baseStart_8177148 baseEnd_8177148 := by
    simpa [prefixWord, tailWord_8177148, baseEnd_8177148] using wordTrace_append hprefix tailTrace_8177148
  have hstable : (prefixWord ++ tailWord_8177148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177148).length < 2 ^ (prefixWord ++ tailWord_8177148).sum := by decide
  have hdescent : baseEnd_8177148 < baseStart_8177148 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177161 : List Nat := [1, 2, 1, 1, 3, 1, 5, 3, 1, 1, 4]
def baseStart_8177161 : Nat := 118140960795 + 8177161 * 2 ^ 59
def prefixEnd_8177161 : Nat := 4983230072969 + 3 ^ 40 * 8177161 * 2
def baseEnd_8177161 : Nat := 4198813982199986553681427

theorem tailTrace_8177161 : CollatzResearch.WordTrace tailWord_8177161 prefixEnd_8177161 4198813982199986553681427 := by
  unfold tailWord_8177161
  simp only [CollatzResearch.WordTrace]
  refine ⟨298245563528549719759051337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198830375685699813172700891 298245563528549719759051337)
  ·
    refine ⟨223684172646412289819288503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298245563528549719759051337 223684172646412289819288503)
    ·
      refine ⟨335526258969618434728932755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223684172646412289819288503 335526258969618434728932755)
      ·
        refine ⟨503289388454427652093399133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335526258969618434728932755 503289388454427652093399133)
        ·
          refine ⟨188733520670410369535024675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 503289388454427652093399133 188733520670410369535024675)
          ·
            refine ⟨283100281005615554302537013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188733520670410369535024675 283100281005615554302537013)
            ·
              refine ⟨26540651344276458215862845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 283100281005615554302537013 26540651344276458215862845)
              ·
                refine ⟨9952744254103671830948567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26540651344276458215862845 9952744254103671830948567)
                ·
                  refine ⟨14929116381155507746422851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9952744254103671830948567 14929116381155507746422851)
                  ·
                    refine ⟨22393674571733261619634277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14929116381155507746422851 22393674571733261619634277)
                    ·
                      refine ⟨4198813982199986553681427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22393674571733261619634277 4198813982199986553681427)
                      ·
                        rfl

theorem cell23_8177161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 1, 4].length) (baseStart_8177161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177161 prefixEnd_8177161 := by exact prefixLift 8177161
  have htrace : WordTrace (prefixWord ++ tailWord_8177161) baseStart_8177161 baseEnd_8177161 := by
    simpa [prefixWord, tailWord_8177161, baseEnd_8177161] using wordTrace_append hprefix tailTrace_8177161
  have hstable : (prefixWord ++ tailWord_8177161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177161).length < 2 ^ (prefixWord ++ tailWord_8177161).sum := by decide
  have hdescent : baseEnd_8177161 < baseStart_8177161 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177171 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 4, 4]
def baseStart_8177171 : Nat := 118140960795 + 8177171 * 2 ^ 59
def prefixEnd_8177171 : Nat := 4983230072969 + 3 ^ 40 * 8177171 * 2
def baseEnd_8177171 : Nat := 1399606372335510504852127

theorem tailTrace_8177171 : CollatzResearch.WordTrace tailWord_8177171 prefixEnd_8177171 1399606372335510504852127 := by
  unfold tailWord_8177171
  simp only [CollatzResearch.WordTrace]
  refine ⟨298245928258513491466915367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198830618839008994311276911 298245928258513491466915367)
  ·
    refine ⟨447368892387770237200373051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298245928258513491466915367 447368892387770237200373051)
    ·
      refine ⟨671053338581655355800559577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447368892387770237200373051 671053338581655355800559577)
      ·
        refine ⟨503290003936241516850419683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 671053338581655355800559577 503290003936241516850419683)
        ·
          refine ⟨754935005904362275275629525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503290003936241516850419683 754935005904362275275629525)
          ·
            refine ⟨17693789200883490826772567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 754935005904362275275629525 17693789200883490826772567)
            ·
              refine ⟨26540683801325236240158851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17693789200883490826772567 26540683801325236240158851)
              ·
                refine ⟨39811025701987854360238277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26540683801325236240158851 39811025701987854360238277)
                ·
                  refine ⟨7464567319122722692544677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39811025701987854360238277 7464567319122722692544677)
                  ·
                    refine ⟨1399606372335510504852127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7464567319122722692544677 1399606372335510504852127)
                    ·
                      rfl

theorem cell23_8177171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 4].length) (baseStart_8177171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177171 prefixEnd_8177171 := by exact prefixLift 8177171
  have htrace : WordTrace (prefixWord ++ tailWord_8177171) baseStart_8177171 baseEnd_8177171 := by
    simpa [prefixWord, tailWord_8177171, baseEnd_8177171] using wordTrace_append hprefix tailTrace_8177171
  have hstable : (prefixWord ++ tailWord_8177171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177171).length < 2 ^ (prefixWord ++ tailWord_8177171).sum := by decide
  have hdescent : baseEnd_8177171 < baseStart_8177171 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177172 : List Nat := [2, 4, 3, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_8177172 : Nat := 118140960795 + 8177172 * 2 ^ 59
def prefixEnd_8177172 : Nat := 4983230072969 + 3 ^ 40 * 8177172 * 2
def baseEnd_8177172 : Nat := 4198819630487186010643877

theorem tailTrace_8177172 : CollatzResearch.WordTrace tailWord_8177172 prefixEnd_8177172 4198819630487186010643877 := by
  unfold tailWord_8177172
  simp only [CollatzResearch.WordTrace]
  refine ⟨149122982365754934318850885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198830643154339912425134513 149122982365754934318850885)
  ·
    refine ⟨27960559193579050184784541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149122982365754934318850885 27960559193579050184784541)
    ·
      refine ⟨10485209697592143819294203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27960559193579050184784541 10485209697592143819294203)
      ·
        refine ⟨15727814546388215728941305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10485209697592143819294203 15727814546388215728941305)
        ·
          refine ⟨11795860909791161796705979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15727814546388215728941305 11795860909791161796705979)
          ·
            refine ⟨17693791364686742695058969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11795860909791161796705979 17693791364686742695058969)
            ·
              refine ⟨13270343523515057021294227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17693791364686742695058969 13270343523515057021294227)
              ·
                refine ⟨19905515285272585531941341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13270343523515057021294227 19905515285272585531941341)
                ·
                  refine ⟨7464568231977219574478003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19905515285272585531941341 7464568231977219574478003)
                  ·
                    refine ⟨11196852347965829361717005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7464568231977219574478003 11196852347965829361717005)
                    ·
                      refine ⟨4198819630487186010643877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11196852347965829361717005 4198819630487186010643877)
                      ·
                        rfl

theorem cell23_8177172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_8177172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177172 prefixEnd_8177172 := by exact prefixLift 8177172
  have htrace : WordTrace (prefixWord ++ tailWord_8177172) baseStart_8177172 baseEnd_8177172 := by
    simpa [prefixWord, tailWord_8177172, baseEnd_8177172] using wordTrace_append hprefix tailTrace_8177172
  have hstable : (prefixWord ++ tailWord_8177172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177172).length < 2 ^ (prefixWord ++ tailWord_8177172).sum := by decide
  have hdescent : baseEnd_8177172 < baseStart_8177172 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177181 : List Nat := [1, 4, 2, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_8177181 : Nat := 118140960795 + 8177181 * 2 ^ 59
def prefixEnd_8177181 : Nat := 4983230072969 + 3 ^ 40 * 8177181 * 2
def baseEnd_8177181 : Nat := 4198824251813076475431335

theorem tailTrace_8177181 : CollatzResearch.WordTrace tailWord_8177181 prefixEnd_8177181 4198824251813076475431335 := by
  unfold tailWord_8177181
  simp only [CollatzResearch.WordTrace]
  refine ⟨298246292988477263174779397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198830861992318175449852931 298246292988477263174779397)
  ·
    refine ⟨55921179935339486845271137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298246292988477263174779397 55921179935339486845271137)
    ·
      refine ⟨41940884951504615133953353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55921179935339486845271137 41940884951504615133953353)
      ·
        refine ⟨31455663713628461350465015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41940884951504615133953353 31455663713628461350465015)
        ·
          refine ⟨47183495570442692025697523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31455663713628461350465015 47183495570442692025697523)
          ·
            refine ⟨70775243355664038038546285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47183495570442692025697523 70775243355664038038546285)
            ·
              refine ⟨26540716258374014264454857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70775243355664038038546285 26540716258374014264454857)
              ·
                refine ⟨19905537193780510698341143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26540716258374014264454857 19905537193780510698341143)
                ·
                  refine ⟨29858305790670766047511715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19905537193780510698341143 29858305790670766047511715)
                  ·
                    refine ⟨44787458686006149071267573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29858305790670766047511715 44787458686006149071267573)
                    ·
                      refine ⟨4198824251813076475431335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44787458686006149071267573 4198824251813076475431335)
                      ·
                        rfl

theorem cell23_8177181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_8177181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177181 prefixEnd_8177181 := by exact prefixLift 8177181
  have htrace : WordTrace (prefixWord ++ tailWord_8177181) baseStart_8177181 baseEnd_8177181 := by
    simpa [prefixWord, tailWord_8177181, baseEnd_8177181] using wordTrace_append hprefix tailTrace_8177181
  have hstable : (prefixWord ++ tailWord_8177181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177181).length < 2 ^ (prefixWord ++ tailWord_8177181).sum := by decide
  have hdescent : baseEnd_8177181 < baseStart_8177181 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177206 : List Nat := [5, 1, 2, 1, 4, 1, 1, 3, 1, 1, 3]
def baseStart_8177206 : Nat := 118140960795 + 8177206 * 2 ^ 59
def prefixEnd_8177206 : Nat := 4983230072969 + 3 ^ 40 * 8177206 * 2
def baseEnd_8177206 : Nat := 4198837088829438877618721

theorem tailTrace_8177206 : CollatzResearch.WordTrace tailWord_8177206 prefixEnd_8177206 4198837088829438877618721 := by
  unfold tailWord_8177206
  simp only [CollatzResearch.WordTrace]
  refine ⟨18640450300836668277777467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198831469875591128296292981 18640450300836668277777467)
  ·
    refine ⟨27960675451255002416666201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18640450300836668277777467 27960675451255002416666201)
    ·
      refine ⟨20970506588441251812499651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27960675451255002416666201 20970506588441251812499651)
      ·
        refine ⟨31455759882661877718749477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20970506588441251812499651 31455759882661877718749477)
        ·
          refine ⟨5897954977999102072265527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31455759882661877718749477 5897954977999102072265527)
          ·
            refine ⟨8846932466998653108398291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5897954977999102072265527 8846932466998653108398291)
            ·
              refine ⟨13270398700497979662597437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8846932466998653108398291 13270398700497979662597437)
              ·
                refine ⟨4976399512686742373474039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13270398700497979662597437 4976399512686742373474039)
                ·
                  refine ⟨7464599269030113560211059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4976399512686742373474039 7464599269030113560211059)
                  ·
                    refine ⟨11196898903545170340316589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7464599269030113560211059 11196898903545170340316589)
                    ·
                      refine ⟨4198837088829438877618721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11196898903545170340316589 4198837088829438877618721)
                      ·
                        rfl

theorem cell23_8177206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_8177206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177206 prefixEnd_8177206 := by exact prefixLift 8177206
  have htrace : WordTrace (prefixWord ++ tailWord_8177206) baseStart_8177206 baseEnd_8177206 := by
    simpa [prefixWord, tailWord_8177206, baseEnd_8177206] using wordTrace_append hprefix tailTrace_8177206
  have hstable : (prefixWord ++ tailWord_8177206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177206).length < 2 ^ (prefixWord ++ tailWord_8177206).sum := by decide
  have hdescent : baseEnd_8177206 < baseStart_8177206 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177228 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 4, 1, 3]
def baseStart_8177228 : Nat := 118140960795 + 8177228 * 2 ^ 59
def prefixEnd_8177228 : Nat := 4983230072969 + 3 ^ 40 * 8177228 * 2
def baseEnd_8177228 : Nat := 4198848385403837791543619

theorem tailTrace_8177228 : CollatzResearch.WordTrace tailWord_8177228 prefixEnd_8177228 4198848385403837791543619 := by
  unfold tailWord_8177228
  simp only [CollatzResearch.WordTrace]
  refine ⟨149124003609653495100870169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198832004812871326801160225 149124003609653495100870169)
  ·
    refine ⟨111843002707240121325652627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149124003609653495100870169 111843002707240121325652627)
    ·
      refine ⟨167764504060860181988478941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111843002707240121325652627 167764504060860181988478941)
      ·
        refine ⟨62911689022822568245679603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167764504060860181988478941 62911689022822568245679603)
        ·
          refine ⟨94367533534233852368519405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62911689022822568245679603 94367533534233852368519405)
          ·
            refine ⟨35387825075337694638194777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94367533534233852368519405 35387825075337694638194777)
            ·
              refine ⟨26540868806503270978646083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35387825075337694638194777 26540868806503270978646083)
              ·
                refine ⟨39811303209754906467969125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26540868806503270978646083 39811303209754906467969125)
                ·
                  refine ⟨7464619351829044962744211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39811303209754906467969125 7464619351829044962744211)
                  ·
                    refine ⟨11196929027743567444116317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7464619351829044962744211 11196929027743567444116317)
                    ·
                      refine ⟨4198848385403837791543619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11196929027743567444116317 4198848385403837791543619)
                      ·
                        rfl

theorem cell23_8177228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_8177228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177228 prefixEnd_8177228 := by exact prefixLift 8177228
  have htrace : WordTrace (prefixWord ++ tailWord_8177228) baseStart_8177228 baseEnd_8177228 := by
    simpa [prefixWord, tailWord_8177228, baseEnd_8177228] using wordTrace_append hprefix tailTrace_8177228
  have hstable : (prefixWord ++ tailWord_8177228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177228).length < 2 ^ (prefixWord ++ tailWord_8177228).sum := by decide
  have hdescent : baseEnd_8177228 < baseStart_8177228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177229 : List Nat := [1, 6, 1, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_8177229 : Nat := 118140960795 + 8177229 * 2 ^ 59
def prefixEnd_8177229 : Nat := 4983230072969 + 3 ^ 40 * 8177229 * 2
def baseEnd_8177229 : Nat := 4198848898884492287631115

theorem tailTrace_8177229 : CollatzResearch.WordTrace tailWord_8177229 prefixEnd_8177229 4198848898884492287631115 := by
  unfold tailWord_8177229
  simp only [CollatzResearch.WordTrace]
  refine ⟨298248043692303367372526741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198832029128202244915017827 298248043692303367372526741)
  ·
    refine ⟨13980377048076720345587191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 298248043692303367372526741 13980377048076720345587191)
    ·
      refine ⟨20970565572115080518380787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13980377048076720345587191 20970565572115080518380787)
      ·
        refine ⟨31455848358172620777571181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20970565572115080518380787 31455848358172620777571181)
        ·
          refine ⟨11795943134314732791589193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31455848358172620777571181 11795943134314732791589193)
          ·
            refine ⟨8846957350736049593691895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11795943134314732791589193 8846957350736049593691895)
            ·
              refine ⟨13270436026104074390537843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8846957350736049593691895 13270436026104074390537843)
              ·
                refine ⟨19905654039156111585806765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13270436026104074390537843 19905654039156111585806765)
                ·
                  refine ⟨7464620264683541844677537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19905654039156111585806765 7464620264683541844677537)
                  ·
                    refine ⟨5598465198512656383508153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7464620264683541844677537 5598465198512656383508153)
                    ·
                      refine ⟨4198848898884492287631115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5598465198512656383508153 4198848898884492287631115)
                      ·
                        rfl

theorem cell23_8177229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_8177229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177229 prefixEnd_8177229 := by exact prefixLift 8177229
  have htrace : WordTrace (prefixWord ++ tailWord_8177229) baseStart_8177229 baseEnd_8177229 := by
    simpa [prefixWord, tailWord_8177229, baseEnd_8177229] using wordTrace_append hprefix tailTrace_8177229
  have hstable : (prefixWord ++ tailWord_8177229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177229).length < 2 ^ (prefixWord ++ tailWord_8177229).sum := by decide
  have hdescent : baseEnd_8177229 < baseStart_8177229 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177255 : List Nat := [1, 1, 5, 1, 1, 1, 5, 2, 1, 3, 2]
def baseStart_8177255 : Nat := 118140960795 + 8177255 * 2 ^ 59
def prefixEnd_8177255 : Nat := 4983230072969 + 3 ^ 40 * 8177255 * 2
def baseEnd_8177255 : Nat := 4198862249381509185905995

theorem tailTrace_8177255 : CollatzResearch.WordTrace tailWord_8177255 prefixEnd_8177255 4198862249381509185905995 := by
  unfold tailWord_8177255
  simp only [CollatzResearch.WordTrace]
  refine ⟨298248991990209173812973219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198832661326806115875315479 298248991990209173812973219)
  ·
    refine ⟨447373487985313760719459829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298248991990209173812973219 447373487985313760719459829)
    ·
      refine ⟨41941264498623165067449359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 447373487985313760719459829 41941264498623165067449359)
      ·
        refine ⟨62911896747934747601174039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41941264498623165067449359 62911896747934747601174039)
        ·
          refine ⟨94367845121902121401761059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62911896747934747601174039 94367845121902121401761059)
          ·
            refine ⟨141551767682853182102641589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94367845121902121401761059 141551767682853182102641589)
            ·
              refine ⟨13270478220267485822122649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141551767682853182102641589 13270478220267485822122649)
              ·
                refine ⟨9952858665200614366591987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13270478220267485822122649 9952858665200614366591987)
                ·
                  refine ⟨14929287997800921549887981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9952858665200614366591987 14929287997800921549887981)
                  ·
                    refine ⟨5598482999175345581207993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14929287997800921549887981 5598482999175345581207993)
                    ·
                      refine ⟨4198862249381509185905995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5598482999175345581207993 4198862249381509185905995)
                      ·
                        rfl

theorem cell23_8177255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_8177255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177255 prefixEnd_8177255 := by exact prefixLift 8177255
  have htrace : WordTrace (prefixWord ++ tailWord_8177255) baseStart_8177255 baseEnd_8177255 := by
    simpa [prefixWord, tailWord_8177255, baseEnd_8177255] using wordTrace_append hprefix tailTrace_8177255
  have hstable : (prefixWord ++ tailWord_8177255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177255).length < 2 ^ (prefixWord ++ tailWord_8177255).sum := by decide
  have hdescent : baseEnd_8177255 < baseStart_8177255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177274 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 11]
def baseStart_8177274 : Nat := 118140960795 + 8177274 * 2 ^ 59
def prefixEnd_8177274 : Nat := 4983230072969 + 3 ^ 40 * 8177274 * 2
def baseEnd_8177274 : Nat := 466541333945993845729823

theorem tailTrace_8177274 : CollatzResearch.WordTrace tailWord_8177274 prefixEnd_8177274 466541333945993845729823 := by
  unfold tailWord_8177274
  simp only [CollatzResearch.WordTrace]
  refine ⟨74562421244285085014478719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198833123318093560038609917 74562421244285085014478719)
  ·
    refine ⟨111843631866427627521718079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74562421244285085014478719 111843631866427627521718079)
    ·
      refine ⟨167765447799641441282577119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111843631866427627521718079 167765447799641441282577119)
      ·
        refine ⟨251648171699462161923865679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167765447799641441282577119 251648171699462161923865679)
        ·
          refine ⟨377472257549193242885798519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251648171699462161923865679 377472257549193242885798519)
          ·
            refine ⟨566208386323789864328697779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377472257549193242885798519 566208386323789864328697779)
            ·
              refine ⟨849312579485684796493046669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566208386323789864328697779 849312579485684796493046669)
              ·
                refine ⟨318492217307131798684892501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 849312579485684796493046669 318492217307131798684892501)
                ·
                  refine ⟨466541333945993845729823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 318492217307131798684892501 466541333945993845729823)
                  ·
                    rfl

theorem cell23_8177274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 11].length) (baseStart_8177274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177274 prefixEnd_8177274 := by exact prefixLift 8177274
  have htrace : WordTrace (prefixWord ++ tailWord_8177274) baseStart_8177274 baseEnd_8177274 := by
    simpa [prefixWord, tailWord_8177274, baseEnd_8177274] using wordTrace_append hprefix tailTrace_8177274
  have hstable : (prefixWord ++ tailWord_8177274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177274).length < 2 ^ (prefixWord ++ tailWord_8177274).sum := by decide
  have hdescent : baseEnd_8177274 < baseStart_8177274 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177308 : List Nat := [2, 2, 3, 2, 3, 1, 1, 2, 7]
def baseStart_8177308 : Nat := 118140960795 + 8177308 * 2 ^ 59
def prefixEnd_8177308 : Nat := 4983230072969 + 3 ^ 40 * 8177308 * 2
def baseEnd_8177308 : Nat := 466543273761799719838139

theorem tailTrace_8177308 : CollatzResearch.WordTrace tailWord_8177308 prefixEnd_8177308 466543273761799719838139 := by
  unfold tailWord_8177308
  simp only [CollatzResearch.WordTrace]
  refine ⟨149125462529508581932326289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198833950039344775909768385 149125462529508581932326289)
  ·
    refine ⟨111844096897131436449244717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149125462529508581932326289 111844096897131436449244717)
    ·
      refine ⟨41941536336424288668466769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111844096897131436449244717 41941536336424288668466769)
      ·
        refine ⟨31456152252318216501350077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41941536336424288668466769 31456152252318216501350077)
        ·
          refine ⟨11796057094619331188006279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31456152252318216501350077 11796057094619331188006279)
          ·
            refine ⟨17694085641928996782009419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11796057094619331188006279 17694085641928996782009419)
            ·
              refine ⟨26541128462893495173014129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17694085641928996782009419 26541128462893495173014129)
              ·
                refine ⟨19905846347170121379760597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26541128462893495173014129 19905846347170121379760597)
                ·
                  refine ⟨466543273761799719838139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19905846347170121379760597 466543273761799719838139)
                  ·
                    rfl

theorem cell23_8177308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 7].length) (baseStart_8177308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177308 prefixEnd_8177308 := by exact prefixLift 8177308
  have htrace : WordTrace (prefixWord ++ tailWord_8177308) baseStart_8177308 baseEnd_8177308 := by
    simpa [prefixWord, tailWord_8177308, baseEnd_8177308] using wordTrace_append hprefix tailTrace_8177308
  have hstable : (prefixWord ++ tailWord_8177308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177308).length < 2 ^ (prefixWord ++ tailWord_8177308).sum := by decide
  have hdescent : baseEnd_8177308 < baseStart_8177308 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177325 : List Nat := [1, 5, 2, 1, 1, 1, 4, 3, 5]
def baseStart_8177325 : Nat := 118140960795 + 8177325 * 2 ^ 59
def prefixEnd_8177325 : Nat := 4983230072969 + 3 ^ 40 * 8177325 * 2
def baseEnd_8177325 : Nat := 466544243669702656892297

theorem tailTrace_8177325 : CollatzResearch.WordTrace tailWord_8177325 prefixEnd_8177325 466544243669702656892297 := by
  unfold tailWord_8177325
  simp only [CollatzResearch.WordTrace]
  refine ⟨298251545099955575768021429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198834363399970383845347619 298251545099955575768021429)
  ·
    refine ⟨27961082353120835228252009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 298251545099955575768021429 27961082353120835228252009)
    ·
      refine ⟨20970811764840626421189007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27961082353120835228252009 20970811764840626421189007)
      ·
        refine ⟨31456217647260939631783511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20970811764840626421189007 31456217647260939631783511)
        ·
          refine ⟨47184326470891409447675267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31456217647260939631783511 47184326470891409447675267)
          ·
            refine ⟨70776489706337114171512901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47184326470891409447675267 70776489706337114171512901)
            ·
              refine ⟨13270591819938208907158669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70776489706337114171512901 13270591819938208907158669)
              ·
                refine ⟨4976471932476828340184501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13270591819938208907158669 4976471932476828340184501)
                ·
                  refine ⟨466544243669702656892297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4976471932476828340184501 466544243669702656892297)
                  ·
                    rfl

theorem cell23_8177325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_8177325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177325 prefixEnd_8177325 := by exact prefixLift 8177325
  have htrace : WordTrace (prefixWord ++ tailWord_8177325) baseStart_8177325 baseEnd_8177325 := by
    simpa [prefixWord, tailWord_8177325, baseEnd_8177325] using wordTrace_append hprefix tailTrace_8177325
  have hstable : (prefixWord ++ tailWord_8177325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177325).length < 2 ^ (prefixWord ++ tailWord_8177325).sum := by decide
  have hdescent : baseEnd_8177325 < baseStart_8177325 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177368 : List Nat := [2, 1, 2, 2, 3, 1, 1, 4, 3, 4]
def baseStart_8177368 : Nat := 118140960795 + 8177368 * 2 ^ 59
def prefixEnd_8177368 : Nat := 4983230072969 + 3 ^ 40 * 8177368 * 2
def baseEnd_8177368 : Nat := 1399640090898489081264325

theorem tailTrace_8177368 : CollatzResearch.WordTrace tailWord_8177368 prefixEnd_8177368 1399640090898489081264325 := by
  unfold tailWord_8177368
  simp only [CollatzResearch.WordTrace]
  refine ⟨149126556719399897055918379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198835408959199862741224505 149126556719399897055918379)
  ·
    refine ⟨223689835079099845583877569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149126556719399897055918379 223689835079099845583877569)
    ·
      refine ⟨167767376309324884187908177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223689835079099845583877569 167767376309324884187908177)
      ·
        refine ⟨125825532231993663140931133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167767376309324884187908177 125825532231993663140931133)
        ·
          refine ⟨47184574586997623677849175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125825532231993663140931133 47184574586997623677849175)
          ·
            refine ⟨70776861880496435516773763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47184574586997623677849175 70776861880496435516773763)
            ·
              refine ⟨106165292820744653275160645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70776861880496435516773763 106165292820744653275160645)
              ·
                refine ⟨19905992403889622489092621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106165292820744653275160645 19905992403889622489092621)
                ·
                  refine ⟨7464747151458608433409733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19905992403889622489092621 7464747151458608433409733)
                  ·
                    refine ⟨1399640090898489081264325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7464747151458608433409733 1399640090898489081264325)
                    ·
                      rfl

theorem cell23_8177368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 3, 4].length) (baseStart_8177368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177368 prefixEnd_8177368 := by exact prefixLift 8177368
  have htrace : WordTrace (prefixWord ++ tailWord_8177368) baseStart_8177368 baseEnd_8177368 := by
    simpa [prefixWord, tailWord_8177368, baseEnd_8177368] using wordTrace_append hprefix tailTrace_8177368
  have hstable : (prefixWord ++ tailWord_8177368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177368).length < 2 ^ (prefixWord ++ tailWord_8177368).sum := by decide
  have hdescent : baseEnd_8177368 < baseStart_8177368 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177381 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 10]
def baseStart_8177381 : Nat := 118140960795 + 8177381 * 2 ^ 59
def prefixEnd_8177381 : Nat := 4983230072969 + 3 ^ 40 * 8177381 * 2
def baseEnd_8177381 : Nat := 466547438660441743658935

theorem tailTrace_8177381 : CollatzResearch.WordTrace tailWord_8177381 prefixEnd_8177381 466547438660441743658935 := by
  unfold tailWord_8177381
  simp only [CollatzResearch.WordTrace]
  refine ⟨298253587587752697332059997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198835725058501798221373331 298253587587752697332059997)
  ·
    refine ⟨111845095345407261499522499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298253587587752697332059997 111845095345407261499522499)
    ·
      refine ⟨167767643018110892249283749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111845095345407261499522499 167767643018110892249283749)
      ·
        refine ⟨31456433065895792296740703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167767643018110892249283749 31456433065895792296740703)
        ·
          refine ⟨47184649598843688445111055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31456433065895792296740703 47184649598843688445111055)
          ·
            refine ⟨70776974398265532667666583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47184649598843688445111055 70776974398265532667666583)
            ·
              refine ⟨106165461597398299001499875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70776974398265532667666583 106165461597398299001499875)
              ·
                refine ⟨159248192396097448502249813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106165461597398299001499875 159248192396097448502249813)
                ·
                  refine ⟨466547438660441743658935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 159248192396097448502249813 466547438660441743658935)
                  ·
                    rfl

theorem cell23_8177381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 10].length) (baseStart_8177381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177381 prefixEnd_8177381 := by exact prefixLift 8177381
  have htrace : WordTrace (prefixWord ++ tailWord_8177381) baseStart_8177381 baseEnd_8177381 := by
    simpa [prefixWord, tailWord_8177381, baseEnd_8177381] using wordTrace_append hprefix tailTrace_8177381
  have hstable : (prefixWord ++ tailWord_8177381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177381).length < 2 ^ (prefixWord ++ tailWord_8177381).sum := by decide
  have hdescent : baseEnd_8177381 < baseStart_8177381 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177398 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 8]
def baseStart_8177398 : Nat := 118140960795 + 8177398 * 2 ^ 59
def prefixEnd_8177398 : Nat := 4983230072969 + 3 ^ 40 * 8177398 * 2
def baseEnd_8177398 : Nat := 466548408568344680713093

theorem tailTrace_8177398 : CollatzResearch.WordTrace tailWord_8177398 prefixEnd_8177398 466548408568344680713093 := by
  unfold tailWord_8177398
  simp only [CollatzResearch.WordTrace]
  refine ⟨18640887976793194327214303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198836138419127406156952565 18640887976793194327214303)
  ·
    refine ⟨27961331965189791490821455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18640887976793194327214303 27961331965189791490821455)
    ·
      refine ⟨41941997947784687236232183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27961331965189791490821455 41941997947784687236232183)
      ·
        refine ⟨62912996921677030854348275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41941997947784687236232183 62912996921677030854348275)
        ·
          refine ⟨94369495382515546281522413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62912996921677030854348275 94369495382515546281522413)
          ·
            refine ⟨35388560768443329855570905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94369495382515546281522413 35388560768443329855570905)
            ·
              refine ⟨26541420576332497391678179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35388560768443329855570905 26541420576332497391678179)
              ·
                refine ⟨39812130864498746087517269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26541420576332497391678179 39812130864498746087517269)
                ·
                  refine ⟨466548408568344680713093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39812130864498746087517269 466548408568344680713093)
                  ·
                    rfl

theorem cell23_8177398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_8177398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177398 prefixEnd_8177398 := by exact prefixLift 8177398
  have htrace : WordTrace (prefixWord ++ tailWord_8177398) baseStart_8177398 baseEnd_8177398 := by
    simpa [prefixWord, tailWord_8177398, baseEnd_8177398] using wordTrace_append hprefix tailTrace_8177398
  have hstable : (prefixWord ++ tailWord_8177398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177398).length < 2 ^ (prefixWord ++ tailWord_8177398).sum := by decide
  have hdescent : baseEnd_8177398 < baseStart_8177398 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177415 : List Nat := [1, 1, 4, 4, 2, 1, 1, 3, 6]
def baseStart_8177415 : Nat := 118140960795 + 8177415 * 2 ^ 59
def prefixEnd_8177415 : Nat := 4983230072969 + 3 ^ 40 * 8177415 * 2
def baseEnd_8177415 : Nat := 466549378476247617767251

theorem tailTrace_8177415 : CollatzResearch.WordTrace tailWord_8177415 prefixEnd_8177415 466549378476247617767251 := by
  unfold tailWord_8177415
  simp only [CollatzResearch.WordTrace]
  refine ⟨298254827669629521138797699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198836551779753014092531799 298254827669629521138797699)
  ·
    refine ⟨447382241504444281708196549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298254827669629521138797699 447382241504444281708196549)
    ·
      refine ⟨83884170282083302820286853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447382241504444281708196549 83884170282083302820286853)
      ·
        refine ⟨15728281927890619278803785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83884170282083302820286853 15728281927890619278803785)
        ·
          refine ⟨11796211445917964459102839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15728281927890619278803785 11796211445917964459102839)
          ·
            refine ⟨17694317168876946688654259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11796211445917964459102839 17694317168876946688654259)
            ·
              refine ⟨26541475753315420032981389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17694317168876946688654259 26541475753315420032981389)
              ·
                refine ⟨9953053407493282512368021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26541475753315420032981389 9953053407493282512368021)
                ·
                  refine ⟨466549378476247617767251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9953053407493282512368021 466549378476247617767251)
                  ·
                    rfl

theorem cell23_8177415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 6].length) (baseStart_8177415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177415 prefixEnd_8177415 := by exact prefixLift 8177415
  have htrace : WordTrace (prefixWord ++ tailWord_8177415) baseStart_8177415 baseEnd_8177415 := by
    simpa [prefixWord, tailWord_8177415, baseEnd_8177415] using wordTrace_append hprefix tailTrace_8177415
  have hstable : (prefixWord ++ tailWord_8177415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177415).length < 2 ^ (prefixWord ++ tailWord_8177415).sum := by decide
  have hdescent : baseEnd_8177415 < baseStart_8177415 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177459 : List Nat := [1, 1, 1, 2, 7, 1, 1, 4, 1, 1, 3]
def baseStart_8177459 : Nat := 118140960795 + 8177459 * 2 ^ 59
def prefixEnd_8177459 : Nat := 4983230072969 + 3 ^ 40 * 8177459 * 2
def baseEnd_8177459 : Nat := 4198966999435026387755057

theorem tailTrace_8177459 : CollatzResearch.WordTrace tailWord_8177459 prefixEnd_8177459 4198966999435026387755057 := by
  unfold tailWord_8177459
  simp only [CollatzResearch.WordTrace]
  refine ⟨298256432481470116653399431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198837621654313411102266287 298256432481470116653399431)
  ·
    refine ⟨447384648722205174980099147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298256432481470116653399431 447384648722205174980099147)
    ·
      refine ⟨671076973083307762470148721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447384648722205174980099147 671076973083307762470148721)
      ·
        refine ⟨503307729812480821852611541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 671076973083307762470148721 503307729812480821852611541)
        ·
          refine ⟨11796274917480019262170583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 503307729812480821852611541 11796274917480019262170583)
          ·
            refine ⟨17694412376220028893255875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11796274917480019262170583 17694412376220028893255875)
            ·
              refine ⟨26541618564330043339883813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17694412376220028893255875 26541618564330043339883813)
              ·
                refine ⟨4976553480811883126228215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26541618564330043339883813 4976553480811883126228215)
                ·
                  refine ⟨7464830221217824689342323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4976553480811883126228215 7464830221217824689342323)
                  ·
                    refine ⟨11197245331826737034013485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7464830221217824689342323 11197245331826737034013485)
                    ·
                      refine ⟨4198966999435026387755057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11197245331826737034013485 4198966999435026387755057)
                      ·
                        rfl

theorem cell23_8177459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 1, 1, 3].length) (baseStart_8177459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177459 prefixEnd_8177459 := by exact prefixLift 8177459
  have htrace : WordTrace (prefixWord ++ tailWord_8177459) baseStart_8177459 baseEnd_8177459 := by
    simpa [prefixWord, tailWord_8177459, baseEnd_8177459] using wordTrace_append hprefix tailTrace_8177459
  have hstable : (prefixWord ++ tailWord_8177459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177459).length < 2 ^ (prefixWord ++ tailWord_8177459).sum := by decide
  have hdescent : baseEnd_8177459 < baseStart_8177459 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177468 : List Nat := [2, 2, 2, 2, 1, 1, 2, 4, 1, 1, 5]
def baseStart_8177468 : Nat := 118140960795 + 8177468 * 2 ^ 59
def prefixEnd_8177468 : Nat := 4983230072969 + 3 ^ 40 * 8177468 * 2
def baseEnd_8177468 : Nat := 4198971620760916852542515

theorem tailTrace_8177468 : CollatzResearch.WordTrace tailWord_8177468 prefixEnd_8177468 4198971620760916852542515 := by
  unfold tailWord_8177468
  simp only [CollatzResearch.WordTrace]
  refine ⟨149128380369218755595238529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198837840492291674126984705 149128380369218755595238529)
  ·
    refine ⟨111846285276914066696428897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149128380369218755595238529 111846285276914066696428897)
    ·
      refine ⟨83884713957685550022321673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111846285276914066696428897 83884713957685550022321673)
      ·
        refine ⟨62913535468264162516741255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83884713957685550022321673 62913535468264162516741255)
        ·
          refine ⟨94370303202396243775111883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62913535468264162516741255 94370303202396243775111883)
          ·
            refine ⟨141555454803594365662667825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94370303202396243775111883 141555454803594365662667825)
            ·
              refine ⟨106166591102695774247000869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141555454803594365662667825 106166591102695774247000869)
              ·
                refine ⟨19906235831755457671312663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106166591102695774247000869 19906235831755457671312663)
                ·
                  refine ⟨29859353747633186506968995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19906235831755457671312663 29859353747633186506968995)
                  ·
                    refine ⟨44789030621449779760453493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29859353747633186506968995 44789030621449779760453493)
                    ·
                      refine ⟨4198971620760916852542515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44789030621449779760453493 4198971620760916852542515)
                      ·
                        rfl

theorem cell23_8177468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_8177468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177468 prefixEnd_8177468 := by exact prefixLift 8177468
  have htrace : WordTrace (prefixWord ++ tailWord_8177468) baseStart_8177468 baseEnd_8177468 := by
    simpa [prefixWord, tailWord_8177468, baseEnd_8177468] using wordTrace_append hprefix tailTrace_8177468
  have hstable : (prefixWord ++ tailWord_8177468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177468).length < 2 ^ (prefixWord ++ tailWord_8177468).sum := by decide
  have hdescent : baseEnd_8177468 < baseStart_8177468 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177475 : List Nat := [1, 1, 1, 3, 1, 5, 2, 3, 2, 4]
def baseStart_8177475 : Nat := 118140960795 + 8177475 * 2 ^ 59
def prefixEnd_8177475 : Nat := 4983230072969 + 3 ^ 40 * 8177475 * 2
def baseEnd_8177475 : Nat := 1399658405041832775051661

theorem tailTrace_8177475 : CollatzResearch.WordTrace tailWord_8177475 prefixEnd_8177475 1399658405041832775051661 := by
  unfold tailWord_8177475
  simp only [CollatzResearch.WordTrace]
  refine ⟨298257016049412151385981879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198838010699608100923987919 298257016049412151385981879)
  ·
    refine ⟨447385524074118227078972819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298257016049412151385981879 447385524074118227078972819)
    ·
      refine ⟨671078286111177340618459229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447385524074118227078972819 671078286111177340618459229)
      ·
        refine ⟨251654357291691502731922211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 671078286111177340618459229 251654357291691502731922211)
        ·
          refine ⟨377481535937537254097883317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251654357291691502731922211 377481535937537254097883317)
          ·
            refine ⟨35388893994144117571676561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 377481535937537254097883317 35388893994144117571676561)
            ·
              refine ⟨26541670495608088178757421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35388893994144117571676561 26541670495608088178757421)
              ·
                refine ⟨9953126435853033067034033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26541670495608088178757421 9953126435853033067034033)
                ·
                  refine ⟨7464844826889774800275525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9953126435853033067034033 7464844826889774800275525)
                  ·
                    refine ⟨1399658405041832775051661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7464844826889774800275525 1399658405041832775051661)
                    ·
                      rfl

theorem cell23_8177475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 4].length) (baseStart_8177475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177475 prefixEnd_8177475 := by exact prefixLift 8177475
  have htrace : WordTrace (prefixWord ++ tailWord_8177475) baseStart_8177475 baseEnd_8177475 := by
    simpa [prefixWord, tailWord_8177475, baseEnd_8177475] using wordTrace_append hprefix tailTrace_8177475
  have hstable : (prefixWord ++ tailWord_8177475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177475).length < 2 ^ (prefixWord ++ tailWord_8177475).sum := by decide
  have hdescent : baseEnd_8177475 < baseStart_8177475 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177482 : List Nat := [3, 1, 2, 1, 1, 1, 5, 2, 3, 2, 2]
def baseStart_8177482 : Nat := 118140960795 + 8177482 * 2 ^ 59
def prefixEnd_8177482 : Nat := 4983230072969 + 3 ^ 40 * 8177482 * 2
def baseEnd_8177482 : Nat := 4198978809490079797767451

theorem tailTrace_8177482 : CollatzResearch.WordTrace tailWord_8177482 prefixEnd_8177482 4198978809490079797767451 := by
  unfold tailWord_8177482
  simp only [CollatzResearch.WordTrace]
  refine ⟨74564317840096697895371675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198838180906924527720991133 74564317840096697895371675)
  ·
    refine ⟨111846476760145046843057513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74564317840096697895371675 111846476760145046843057513)
    ·
      refine ⟨83884857570108785132293135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111846476760145046843057513 83884857570108785132293135)
      ·
        refine ⟨125827286355163177698439703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83884857570108785132293135 125827286355163177698439703)
        ·
          refine ⟨188740929532744766547659555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125827286355163177698439703 188740929532744766547659555)
          ·
            refine ⟨283111394299117149821489333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188740929532744766547659555 283111394299117149821489333)
            ·
              refine ⟨26541693215542232795764625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 283111394299117149821489333 26541693215542232795764625)
              ·
                refine ⟨19906269911656674596823469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26541693215542232795764625 19906269911656674596823469)
                ·
                  refine ⟨7464851216871252973808801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19906269911656674596823469 7464851216871252973808801)
                  ·
                    refine ⟨5598638412653439730356601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7464851216871252973808801 5598638412653439730356601)
                    ·
                      refine ⟨4198978809490079797767451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5598638412653439730356601 4198978809490079797767451)
                      ·
                        rfl

theorem cell23_8177482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_8177482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177482 prefixEnd_8177482 := by exact prefixLift 8177482
  have htrace : WordTrace (prefixWord ++ tailWord_8177482) baseStart_8177482 baseEnd_8177482 := by
    simpa [prefixWord, tailWord_8177482, baseEnd_8177482] using wordTrace_append hprefix tailTrace_8177482
  have hstable : (prefixWord ++ tailWord_8177482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177482).length < 2 ^ (prefixWord ++ tailWord_8177482).sum := by decide
  have hdescent : baseEnd_8177482 < baseStart_8177482 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177526 : List Nat := [5, 1, 1, 3, 2, 1, 3, 1, 2, 4]
def baseStart_8177526 : Nat := 118140960795 + 8177526 * 2 ^ 59
def prefixEnd_8177526 : Nat := 4983230072969 + 3 ^ 40 * 8177526 * 2
def baseEnd_8177526 : Nat := 1399667134212959208539083

theorem tailTrace_8177526 : CollatzResearch.WordTrace tailWord_8177526 prefixEnd_8177526 1399667134212959208539083 := by
  unfold tailWord_8177526
  simp only [CollatzResearch.WordTrace]
  refine ⟨18641179760764211693505527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198839250781484924730725621 18641179760764211693505527)
  ·
    refine ⟨27961769641146317540258291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18641179760764211693505527 27961769641146317540258291)
    ·
      refine ⟨41942654461719476310387437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27961769641146317540258291 41942654461719476310387437)
      ·
        refine ⟨15728495423144803616395289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41942654461719476310387437 15728495423144803616395289)
        ·
          refine ⟨11796371567358602712296467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15728495423144803616395289 11796371567358602712296467)
          ·
            refine ⟨17694557351037904068444701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11796371567358602712296467 17694557351037904068444701)
            ·
              refine ⟨6635459006639214025666763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17694557351037904068444701 6635459006639214025666763)
              ·
                refine ⟨9953188509958821038500145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6635459006639214025666763 9953188509958821038500145)
                ·
                  refine ⟨7464891382469115778875109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9953188509958821038500145 7464891382469115778875109)
                  ·
                    refine ⟨1399667134212959208539083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7464891382469115778875109 1399667134212959208539083)
                    ·
                      rfl

theorem cell23_8177526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_8177526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177526 prefixEnd_8177526 := by exact prefixLift 8177526
  have htrace : WordTrace (prefixWord ++ tailWord_8177526) baseStart_8177526 baseEnd_8177526 := by
    simpa [prefixWord, tailWord_8177526, baseEnd_8177526] using wordTrace_append hprefix tailTrace_8177526
  have hstable : (prefixWord ++ tailWord_8177526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177526).length < 2 ^ (prefixWord ++ tailWord_8177526).sum := by decide
  have hdescent : baseEnd_8177526 < baseStart_8177526 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177550 : List Nat := [4, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2]
def baseStart_8177550 : Nat := 118140960795 + 8177550 * 2 ^ 59
def prefixEnd_8177550 : Nat := 4983230072969 + 3 ^ 40 * 8177550 * 2
def baseEnd_8177550 : Nat := 4199013726174585531717139

theorem tailTrace_8177550 : CollatzResearch.WordTrace tailWord_8177550 prefixEnd_8177550 4199013726174585531717139 := by
  unfold tailWord_8177550
  simp only [CollatzResearch.WordTrace]
  refine ⟨37282468940517554899370263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198839834349426959463308069 37282468940517554899370263)
  ·
    refine ⟨55923703410776332349055395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37282468940517554899370263 55923703410776332349055395)
    ·
      refine ⟨83885555116164498523583093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55923703410776332349055395 83885555116164498523583093)
      ·
        refine ⟨7864270792140421736585915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83885555116164498523583093 7864270792140421736585915)
        ·
          refine ⟨11796406188210632604878873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7864270792140421736585915 11796406188210632604878873)
          ·
            refine ⟨8847304641157974453659155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11796406188210632604878873 8847304641157974453659155)
            ·
              refine ⟨13270956961736961680488733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8847304641157974453659155 13270956961736961680488733)
              ·
                refine ⟨4976608860651360630183275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13270956961736961680488733 4976608860651360630183275)
                ·
                  refine ⟨7464913290977040945274913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4976608860651360630183275 7464913290977040945274913)
                  ·
                    refine ⟨5598684968232780708956185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7464913290977040945274913 5598684968232780708956185)
                    ·
                      refine ⟨4199013726174585531717139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5598684968232780708956185 4199013726174585531717139)
                      ·
                        rfl

theorem cell23_8177550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_8177550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177550 prefixEnd_8177550 := by exact prefixLift 8177550
  have htrace : WordTrace (prefixWord ++ tailWord_8177550) baseStart_8177550 baseEnd_8177550 := by
    simpa [prefixWord, tailWord_8177550, baseEnd_8177550] using wordTrace_append hprefix tailTrace_8177550
  have hstable : (prefixWord ++ tailWord_8177550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177550).length < 2 ^ (prefixWord ++ tailWord_8177550).sum := by decide
  have hdescent : baseEnd_8177550 < baseStart_8177550 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177629 : List Nat := [1, 4, 3, 1, 3, 1, 1, 4, 5]
def baseStart_8177629 : Nat := 118140960795 + 8177629 * 2 ^ 59
def prefixEnd_8177629 : Nat := 4983230072969 + 3 ^ 40 * 8177629 * 2
def baseEnd_8177629 : Nat := 466561587905143413625475

theorem tailTrace_8177629 : CollatzResearch.WordTrace tailWord_8177629 prefixEnd_8177629 466561587905143413625475 := by
  unfold tailWord_8177629
  simp only [CollatzResearch.WordTrace]
  refine ⟨298262632890854235687087941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198841755260569490458058627 298262632890854235687087941)
  ·
    refine ⟨55924243667035169191328989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298262632890854235687087941 55924243667035169191328989)
    ·
      refine ⟨20971591375138188446748371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55924243667035169191328989 20971591375138188446748371)
      ·
        refine ⟨31457387062707282670122557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20971591375138188446748371 31457387062707282670122557)
        ·
          refine ⟨11796520148515231001295959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31457387062707282670122557 11796520148515231001295959)
          ·
            refine ⟨17694780222772846501943939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11796520148515231001295959 17694780222772846501943939)
            ·
              refine ⟨26542170334159269752915909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17694780222772846501943939 26542170334159269752915909)
              ·
                refine ⟨4976656937654863078671733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26542170334159269752915909 4976656937654863078671733)
                ·
                  refine ⟨466561587905143413625475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4976656937654863078671733 466561587905143413625475)
                  ·
                    rfl

theorem cell23_8177629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_8177629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177629 prefixEnd_8177629 := by exact prefixLift 8177629
  have htrace : WordTrace (prefixWord ++ tailWord_8177629) baseStart_8177629 baseEnd_8177629 := by
    simpa [prefixWord, tailWord_8177629, baseEnd_8177629] using wordTrace_append hprefix tailTrace_8177629
  have hstable : (prefixWord ++ tailWord_8177629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177629).length < 2 ^ (prefixWord ++ tailWord_8177629).sum := by decide
  have hdescent : baseEnd_8177629 < baseStart_8177629 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177635 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 5]
def baseStart_8177635 : Nat := 118140960795 + 8177635 * 2 ^ 59
def prefixEnd_8177635 : Nat := 4983230072969 + 3 ^ 40 * 8177635 * 2
def baseEnd_8177635 : Nat := 4199057372030217699154247

theorem tailTrace_8177635 : CollatzResearch.WordTrace tailWord_8177635 prefixEnd_8177635 4199057372030217699154247 := by
  unfold tailWord_8177635
  simp only [CollatzResearch.WordTrace]
  refine ⟨298262851728832498711806359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198841901152554999141204239 298262851728832498711806359)
  ·
    refine ⟨447394277593248748067709539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298262851728832498711806359 447394277593248748067709539)
    ·
      refine ⟨671091416389873122101564309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447394277593248748067709539 671091416389873122101564309)
      ·
        refine ⟨31457410143275302598510827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 671091416389873122101564309 31457410143275302598510827)
        ·
          refine ⟨47186115214912953897766241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31457410143275302598510827 47186115214912953897766241)
          ·
            refine ⟨35389586411184715423324681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47186115214912953897766241 35389586411184715423324681)
            ·
              refine ⟨26542189808388536567493511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35389586411184715423324681 26542189808388536567493511)
              ·
                refine ⟨39813284712582804851240267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26542189808388536567493511 39813284712582804851240267)
                ·
                  refine ⟨59719927068874207276860401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39813284712582804851240267 59719927068874207276860401)
                  ·
                    refine ⟨44789945301655655457645301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59719927068874207276860401 44789945301655655457645301)
                    ·
                      refine ⟨4199057372030217699154247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44789945301655655457645301 4199057372030217699154247)
                      ·
                        rfl

theorem cell23_8177635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_8177635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177635 prefixEnd_8177635 := by exact prefixLift 8177635
  have htrace : WordTrace (prefixWord ++ tailWord_8177635) baseStart_8177635 baseEnd_8177635 := by
    simpa [prefixWord, tailWord_8177635, baseEnd_8177635] using wordTrace_append hprefix tailTrace_8177635
  have hstable : (prefixWord ++ tailWord_8177635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177635).length < 2 ^ (prefixWord ++ tailWord_8177635).sum := by decide
  have hdescent : baseEnd_8177635 < baseStart_8177635 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177715 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 3, 5]
def baseStart_8177715 : Nat := 118140960795 + 8177715 * 2 ^ 59
def prefixEnd_8177715 : Nat := 4983230072969 + 3 ^ 40 * 8177715 * 2
def baseEnd_8177715 : Nat := 1399699483494192462051293

theorem tailTrace_8177715 : CollatzResearch.WordTrace tailWord_8177715 prefixEnd_8177715 1399699483494192462051293 := by
  unfold tailWord_8177715
  simp only [CollatzResearch.WordTrace]
  refine ⟨298265769568542672374718599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198843846379028448249812399 298265769568542672374718599)
  ·
    refine ⟨447398654352814008562077899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298265769568542672374718599 447398654352814008562077899)
    ·
      refine ⟨671097981529221012843116849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447398654352814008562077899 671097981529221012843116849)
      ·
        refine ⟨503323486146915759632337637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 671097981529221012843116849 503323486146915759632337637)
        ·
          refine ⟨94373153652546704931063307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 503323486146915759632337637 94373153652546704931063307)
          ·
            refine ⟨141559730478820057396594961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94373153652546704931063307 141559730478820057396594961)
            ·
              refine ⟨106169797859115043047446221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141559730478820057396594961 106169797859115043047446221)
              ·
                refine ⟨39813674197168141142792333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106169797859115043047446221 39813674197168141142792333)
                ·
                  refine ⟨14930127823938052928547125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39813674197168141142792333 14930127823938052928547125)
                  ·
                    refine ⟨1399699483494192462051293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14930127823938052928547125 1399699483494192462051293)
                    ·
                      rfl

theorem cell23_8177715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 5].length) (baseStart_8177715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177715 prefixEnd_8177715 := by exact prefixLift 8177715
  have htrace : WordTrace (prefixWord ++ tailWord_8177715) baseStart_8177715 baseEnd_8177715 := by
    simpa [prefixWord, tailWord_8177715, baseEnd_8177715] using wordTrace_append hprefix tailTrace_8177715
  have hstable : (prefixWord ++ tailWord_8177715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177715).length < 2 ^ (prefixWord ++ tailWord_8177715).sum := by decide
  have hdescent : baseEnd_8177715 < baseStart_8177715 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177769 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 5, 2, 2]
def baseStart_8177769 : Nat := 118140960795 + 8177769 * 2 ^ 59
def prefixEnd_8177769 : Nat := 4983230072969 + 3 ^ 40 * 8177769 * 2
def baseEnd_8177769 : Nat := 4199126178437920174878631

theorem tailTrace_8177769 : CollatzResearch.WordTrace tailWord_8177769 prefixEnd_8177769 4199126178437920174878631 := by
  unfold tailWord_8177769
  simp only [CollatzResearch.WordTrace]
  refine ⟨298267739110347039597184361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198845159406898026398122907 298267739110347039597184361)
  ·
    refine ⟨223700804332760279697888271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298267739110347039597184361 223700804332760279697888271)
    ·
      refine ⟨335551206499140419546832407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223700804332760279697888271 335551206499140419546832407)
      ·
        refine ⟨503326809748710629320248611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335551206499140419546832407 503326809748710629320248611)
        ·
          refine ⟨754990214623065943980372917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503326809748710629320248611 754990214623065943980372917)
          ·
            refine ⟨70780332620912432248159961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 754990214623065943980372917 70780332620912432248159961)
            ·
              refine ⟨53085249465684324186119971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70780332620912432248159961 53085249465684324186119971)
              ·
                refine ⟨79627874198526486279179957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53085249465684324186119971 79627874198526486279179957)
                ·
                  refine ⟨7465113206111858088673121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79627874198526486279179957 7465113206111858088673121)
                  ·
                    refine ⟨5598834904583893566504841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7465113206111858088673121 5598834904583893566504841)
                    ·
                      refine ⟨4199126178437920174878631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5598834904583893566504841 4199126178437920174878631)
                      ·
                        rfl

theorem cell23_8177769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 2, 2].length) (baseStart_8177769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177769 prefixEnd_8177769 := by exact prefixLift 8177769
  have htrace : WordTrace (prefixWord ++ tailWord_8177769) baseStart_8177769 baseEnd_8177769 := by
    simpa [prefixWord, tailWord_8177769, baseEnd_8177769] using wordTrace_append hprefix tailTrace_8177769
  have hstable : (prefixWord ++ tailWord_8177769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177769).length < 2 ^ (prefixWord ++ tailWord_8177769).sum := by decide
  have hdescent : baseEnd_8177769 < baseStart_8177769 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177775 : List Nat := [1, 1, 2, 1, 3, 4, 2, 9]
def baseStart_8177775 : Nat := 118140960795 + 8177775 * 2 ^ 59
def prefixEnd_8177775 : Nat := 4983230072969 + 3 ^ 40 * 8177775 * 2
def baseEnd_8177775 : Nat := 155523305900809153755689

theorem tailTrace_8177775 : CollatzResearch.WordTrace tailWord_8177775 prefixEnd_8177775 155523305900809153755689 := by
  unfold tailWord_8177775
  simp only [CollatzResearch.WordTrace]
  refine ⟨298267957948325302621902779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198845305298883535081268519 298267957948325302621902779)
  ·
    refine ⟨447401936922487953932854169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298267957948325302621902779 447401936922487953932854169)
    ·
      refine ⟨335551452691865965449640627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447401936922487953932854169 335551452691865965449640627)
      ·
        refine ⟨503327179037798948174460941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335551452691865965449640627 503327179037798948174460941)
        ·
          refine ⟨188747692139174605565422853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 503327179037798948174460941 188747692139174605565422853)
          ·
            refine ⟨35390192276095238543516785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188747692139174605565422853 35390192276095238543516785)
            ·
              refine ⟨26542644207071428907637589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35390192276095238543516785 26542644207071428907637589)
              ·
                refine ⟨155523305900809153755689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26542644207071428907637589 155523305900809153755689)
                ·
                  rfl

theorem cell23_8177775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 9].length) (baseStart_8177775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177775 prefixEnd_8177775 := by exact prefixLift 8177775
  have htrace : WordTrace (prefixWord ++ tailWord_8177775) baseStart_8177775 baseEnd_8177775 := by
    simpa [prefixWord, tailWord_8177775, baseEnd_8177775] using wordTrace_append hprefix tailTrace_8177775
  have hstable : (prefixWord ++ tailWord_8177775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177775).length < 2 ^ (prefixWord ++ tailWord_8177775).sum := by decide
  have hdescent : baseEnd_8177775 < baseStart_8177775 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177789 : List Nat := [1, 4, 1, 1, 3, 4, 1, 1, 1, 1, 5]
def baseStart_8177789 : Nat := 118140960795 + 8177789 * 2 ^ 59
def prefixEnd_8177789 : Nat := 4983230072969 + 3 ^ 40 * 8177789 * 2
def baseEnd_8177789 : Nat := 4199136448051010096628539

theorem tailTrace_8177789 : CollatzResearch.WordTrace tailWord_8177789 prefixEnd_8177789 4199136448051010096628539 := by
  unfold tailWord_8177789
  simp only [CollatzResearch.WordTrace]
  refine ⟨298268468570274583012912421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198845645713516388675274947 298268468570274583012912421)
  ·
    refine ⟨55925337856926484314921079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298268468570274583012912421 55925337856926484314921079)
    ·
      refine ⟨83888006785389726472381619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55925337856926484314921079 83888006785389726472381619)
      ·
        refine ⟨125832010178084589708572429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83888006785389726472381619 125832010178084589708572429)
        ·
          refine ⟨47187003816781721140714661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125832010178084589708572429 47187003816781721140714661)
          ·
            refine ⟨8847563215646572713883999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47187003816781721140714661 8847563215646572713883999)
            ·
              refine ⟨13271344823469859070825999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8847563215646572713883999 13271344823469859070825999)
              ·
                refine ⟨19907017235204788606238999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13271344823469859070825999 19907017235204788606238999)
                ·
                  refine ⟨29860525852807182909358499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19907017235204788606238999 29860525852807182909358499)
                  ·
                    refine ⟨44790788779210774364037749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29860525852807182909358499 44790788779210774364037749)
                    ·
                      refine ⟨4199136448051010096628539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44790788779210774364037749 4199136448051010096628539)
                      ·
                        rfl

theorem cell23_8177789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_8177789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177789 prefixEnd_8177789 := by exact prefixLift 8177789
  have htrace : WordTrace (prefixWord ++ tailWord_8177789) baseStart_8177789 baseEnd_8177789 := by
    simpa [prefixWord, tailWord_8177789, baseEnd_8177789] using wordTrace_append hprefix tailTrace_8177789
  have hstable : (prefixWord ++ tailWord_8177789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177789).length < 2 ^ (prefixWord ++ tailWord_8177789).sum := by decide
  have hdescent : baseEnd_8177789 < baseStart_8177789 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177819 : List Nat := [1, 1, 1, 1, 1, 1, 2, 9, 2, 1, 3]
def baseStart_8177819 : Nat := 118140960795 + 8177819 * 2 ^ 59
def prefixEnd_8177819 : Nat := 4983230072969 + 3 ^ 40 * 8177819 * 2
def baseEnd_8177819 : Nat := 4199151852470644979253401

theorem tailTrace_8177819 : CollatzResearch.WordTrace tailWord_8177819 prefixEnd_8177819 4199151852470644979253401 := by
  unfold tailWord_8177819
  simp only [CollatzResearch.WordTrace]
  refine ⟨298269562760165898136504511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198846375173443932091003007 298269562760165898136504511)
  ·
    refine ⟨447404344140248847204756767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298269562760165898136504511 447404344140248847204756767)
    ·
      refine ⟨671106516210373270807135151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447404344140248847204756767 671106516210373270807135151)
      ·
        refine ⟨1006659774315559906210702727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671106516210373270807135151 1006659774315559906210702727)
        ·
          refine ⟨1509989661473339859316054091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1006659774315559906210702727 1509989661473339859316054091)
          ·
            refine ⟨2264984492210009788974081137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1509989661473339859316054091 2264984492210009788974081137)
            ·
              refine ⟨1698738369157507341730560853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2264984492210009788974081137 1698738369157507341730560853)
              ·
                refine ⟨9953545131782269580452505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1698738369157507341730560853 9953545131782269580452505)
                ·
                  refine ⟨7465158848836702185339379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9953545131782269580452505 7465158848836702185339379)
                  ·
                    refine ⟨11197738273255053278009069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7465158848836702185339379 11197738273255053278009069)
                    ·
                      refine ⟨4199151852470644979253401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11197738273255053278009069 4199151852470644979253401)
                      ·
                        rfl

theorem cell23_8177819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 1, 3].length) (baseStart_8177819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177819 prefixEnd_8177819 := by exact prefixLift 8177819
  have htrace : WordTrace (prefixWord ++ tailWord_8177819) baseStart_8177819 baseEnd_8177819 := by
    simpa [prefixWord, tailWord_8177819, baseEnd_8177819] using wordTrace_append hprefix tailTrace_8177819
  have hstable : (prefixWord ++ tailWord_8177819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177819).length < 2 ^ (prefixWord ++ tailWord_8177819).sum := by decide
  have hdescent : baseEnd_8177819 < baseStart_8177819 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177829 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 3, 3, 2]
def baseStart_8177829 : Nat := 118140960795 + 8177829 * 2 ^ 59
def prefixEnd_8177829 : Nat := 4983230072969 + 3 ^ 40 * 8177829 * 2
def baseEnd_8177829 : Nat := 4199156987277189940128355

theorem tailTrace_8177829 : CollatzResearch.WordTrace tailWord_8177829 prefixEnd_8177829 4199156987277189940128355 := by
  unfold tailWord_8177829
  simp only [CollatzResearch.WordTrace]
  refine ⟨298269927490129669844368541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198846618326753113229579027 298269927490129669844368541)
  ·
    refine ⟨111851222808798626191638203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298269927490129669844368541 111851222808798626191638203)
    ·
      refine ⟨167776834213197939287457305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111851222808798626191638203 167776834213197939287457305)
      ·
        refine ⟨125832625659898454465592979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167776834213197939287457305 125832625659898454465592979)
        ·
          refine ⟨188748938489847681698389469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125832625659898454465592979 188748938489847681698389469)
          ·
            refine ⟨70780851933692880636896051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188748938489847681698389469 70780851933692880636896051)
            ·
              refine ⟨106171277900539320955344077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70780851933692880636896051 106171277900539320955344077)
              ·
                refine ⟨39814229212702245358254029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106171277900539320955344077 39814229212702245358254029)
                ·
                  refine ⟨14930335954763342009345261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39814229212702245358254029 14930335954763342009345261)
                  ·
                    refine ⟨5598875983036253253504473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14930335954763342009345261 5598875983036253253504473)
                    ·
                      refine ⟨4199156987277189940128355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5598875983036253253504473 4199156987277189940128355)
                      ·
                        rfl

theorem cell23_8177829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_8177829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177829 prefixEnd_8177829 := by exact prefixLift 8177829
  have htrace : WordTrace (prefixWord ++ tailWord_8177829) baseStart_8177829 baseEnd_8177829 := by
    simpa [prefixWord, tailWord_8177829, baseEnd_8177829] using wordTrace_append hprefix tailTrace_8177829
  have hstable : (prefixWord ++ tailWord_8177829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177829).length < 2 ^ (prefixWord ++ tailWord_8177829).sum := by decide
  have hdescent : baseEnd_8177829 < baseStart_8177829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177882 : List Nat := [3, 1, 1, 2, 2, 1, 4, 2, 7]
def baseStart_8177882 : Nat := 118140960795 + 8177882 * 2 ^ 59
def prefixEnd_8177882 : Nat := 4983230072969 + 3 ^ 40 * 8177882 * 2
def baseEnd_8177882 : Nat := 466576022416875359196179

theorem tailTrace_8177882 : CollatzResearch.WordTrace tailWord_8177882 prefixEnd_8177882 466576022416875359196179 := by
  unfold tailWord_8177882
  simp only [CollatzResearch.WordTrace]
  refine ⟨74567965139734414974011975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198847907039291773264031933 74567965139734414974011975)
  ·
    refine ⟨111851947709601622461017963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74567965139734414974011975 111851947709601622461017963)
    ·
      refine ⟨167777921564402433691526945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111851947709601622461017963 167777921564402433691526945)
      ·
        refine ⟨125833441173301825268645209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167777921564402433691526945 125833441173301825268645209)
        ·
          refine ⟨94375080879976368951483907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125833441173301825268645209 94375080879976368951483907)
          ·
            refine ⟨141562621319964553427225861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94375080879976368951483907 141562621319964553427225861)
            ·
              refine ⟨26542991497493353767604849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141562621319964553427225861 26542991497493353767604849)
              ·
                refine ⟨19907243623120015325703637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26542991497493353767604849 19907243623120015325703637)
                ·
                  refine ⟨466576022416875359196179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19907243623120015325703637 466576022416875359196179)
                  ·
                    rfl

theorem cell23_8177882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 7].length) (baseStart_8177882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177882 prefixEnd_8177882 := by exact prefixLift 8177882
  have htrace : WordTrace (prefixWord ++ tailWord_8177882) baseStart_8177882 baseEnd_8177882 := by
    simpa [prefixWord, tailWord_8177882, baseEnd_8177882] using wordTrace_append hprefix tailTrace_8177882
  have hstable : (prefixWord ++ tailWord_8177882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177882).length < 2 ^ (prefixWord ++ tailWord_8177882).sum := by decide
  have hdescent : baseEnd_8177882 < baseStart_8177882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177919 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 2, 5, 2]
def baseStart_8177919 : Nat := 118140960795 + 8177919 * 2 ^ 59
def prefixEnd_8177919 : Nat := 4983230072969 + 3 ^ 40 * 8177919 * 2
def baseEnd_8177919 : Nat := 4199203200536094588002941

theorem tailTrace_8177919 : CollatzResearch.WordTrace tailWord_8177919 prefixEnd_8177919 4199203200536094588002941 := by
  unfold tailWord_8177919
  simp only [CollatzResearch.WordTrace]
  refine ⟨298273210059803615215144811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198848806706535743476763207 298273210059803615215144811)
  ·
    refine ⟨447409815089705422822717217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298273210059803615215144811 447409815089705422822717217)
    ·
      refine ⟨335557361317279067117037913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447409815089705422822717217 335557361317279067117037913)
      ·
        refine ⟨251668020987959300337778435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335557361317279067117037913 251668020987959300337778435)
        ·
          refine ⟨377502031481938950506667653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251668020987959300337778435 377502031481938950506667653)
          ·
            refine ⟨70781630902863553220000185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 377502031481938950506667653 70781630902863553220000185)
            ·
              refine ⟨53086223177147664915000139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70781630902863553220000185 53086223177147664915000139)
              ·
                refine ⟨79629334765721497372500209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53086223177147664915000139 79629334765721497372500209)
                ·
                  refine ⟨59722001074291123029375157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79629334765721497372500209 59722001074291123029375157)
                  ·
                    refine ⟨5598937600714792784003921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59722001074291123029375157 5598937600714792784003921)
                    ·
                      refine ⟨4199203200536094588002941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5598937600714792784003921 4199203200536094588002941)
                      ·
                        rfl

theorem cell23_8177919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 5, 2].length) (baseStart_8177919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177919 prefixEnd_8177919 := by exact prefixLift 8177919
  have htrace : WordTrace (prefixWord ++ tailWord_8177919) baseStart_8177919 baseEnd_8177919 := by
    simpa [prefixWord, tailWord_8177919, baseEnd_8177919] using wordTrace_append hprefix tailTrace_8177919
  have hstable : (prefixWord ++ tailWord_8177919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177919).length < 2 ^ (prefixWord ++ tailWord_8177919).sum := by decide
  have hdescent : baseEnd_8177919 < baseStart_8177919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8177946 : List Nat := [3, 1, 1, 3, 4, 1, 2, 1, 2, 5]
def baseStart_8177946 : Nat := 118140960795 + 8177946 * 2 ^ 59
def prefixEnd_8177946 : Nat := 4983230072969 + 3 ^ 40 * 8177946 * 2
def baseEnd_8177946 : Nat := 1399739021504588660788439

theorem tailTrace_8177946 : CollatzResearch.WordTrace tailWord_8177946 prefixEnd_8177946 1399739021504588660788439 := by
  unfold tailWord_8177946
  simp only [CollatzResearch.WordTrace]
  refine ⟨74568548707676449706594423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198849463220470532550918461 74568548707676449706594423)
  ·
    refine ⟨111852823061514674559891635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74568548707676449706594423 111852823061514674559891635)
    ·
      refine ⟨167779234592272011839837453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111852823061514674559891635 167779234592272011839837453)
      ·
        refine ⟨62917212972102004439939045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167779234592272011839837453 62917212972102004439939045)
        ·
          refine ⟨11796977432269125832488571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62917212972102004439939045 11796977432269125832488571)
          ·
            refine ⟨17695466148403688748732857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11796977432269125832488571 17695466148403688748732857)
            ·
              refine ⟨13271599611302766561549643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17695466148403688748732857 13271599611302766561549643)
              ·
                refine ⟨19907399416954149842324465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13271599611302766561549643 19907399416954149842324465)
                ·
                  refine ⟨14930549562715612381743349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19907399416954149842324465 14930549562715612381743349)
                  ·
                    refine ⟨1399739021504588660788439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14930549562715612381743349 1399739021504588660788439)
                    ·
                      rfl

theorem cell23_8177946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_8177946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8177946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8177946 prefixEnd_8177946 := by exact prefixLift 8177946
  have htrace : WordTrace (prefixWord ++ tailWord_8177946) baseStart_8177946 baseEnd_8177946 := by
    simpa [prefixWord, tailWord_8177946, baseEnd_8177946] using wordTrace_append hprefix tailTrace_8177946
  have hstable : (prefixWord ++ tailWord_8177946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8177946).length < 2 ^ (prefixWord ++ tailWord_8177946).sum := by decide
  have hdescent : baseEnd_8177946 < baseStart_8177946 := by decide
  rcases family_descends (prefixWord ++ tailWord_8177946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178039 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 4]
def baseStart_8178039 : Nat := 118140960795 + 8178039 * 2 ^ 59
def prefixEnd_8178039 : Nat := 4983230072969 + 3 ^ 40 * 8178039 * 2
def baseEnd_8178039 : Nat := 4199264818214634118502389

theorem tailTrace_8178039 : CollatzResearch.WordTrace tailWord_8178039 prefixEnd_8178039 4199264818214634118502389 := by
  unfold tailWord_8178039
  simp only [CollatzResearch.WordTrace]
  refine ⟨298277586819368875709513171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198851724546245917139675447 298277586819368875709513171)
  ·
    refine ⟨447416380229053313564269757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298277586819368875709513171 447416380229053313564269757)
    ·
      refine ⟨167781142585894992586601159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447416380229053313564269757 167781142585894992586601159)
      ·
        refine ⟨251671713878842488879901739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167781142585894992586601159 251671713878842488879901739)
        ·
          refine ⟨377507570818263733319852609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251671713878842488879901739 377507570818263733319852609)
          ·
            refine ⟨283130678113697799989889457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377507570818263733319852609 283130678113697799989889457)
            ·
              refine ⟨212348008585273349992417093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283130678113697799989889457 212348008585273349992417093)
              ·
                refine ⟨39815251609738753123578205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212348008585273349992417093 39815251609738753123578205)
                ·
                  refine ⟨14930719353652032421341827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39815251609738753123578205 14930719353652032421341827)
                  ·
                    refine ⟨22396079030478048632012741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14930719353652032421341827 22396079030478048632012741)
                    ·
                      refine ⟨4199264818214634118502389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22396079030478048632012741 4199264818214634118502389)
                      ·
                        rfl

theorem cell23_8178039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_8178039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178039 prefixEnd_8178039 := by exact prefixLift 8178039
  have htrace : WordTrace (prefixWord ++ tailWord_8178039) baseStart_8178039 baseEnd_8178039 := by
    simpa [prefixWord, tailWord_8178039, baseEnd_8178039] using wordTrace_append hprefix tailTrace_8178039
  have hstable : (prefixWord ++ tailWord_8178039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178039).length < 2 ^ (prefixWord ++ tailWord_8178039).sum := by decide
  have hdescent : baseEnd_8178039 < baseStart_8178039 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178056 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 2, 6, 2]
def baseStart_8178056 : Nat := 118140960795 + 8178056 * 2 ^ 59
def prefixEnd_8178056 : Nat := 4983230072969 + 3 ^ 40 * 8178056 * 2
def baseEnd_8178056 : Nat := 4199273547385760551989811

theorem tailTrace_8178056 : CollatzResearch.WordTrace tailWord_8178056 prefixEnd_8178056 4199273547385760551989811 := by
  unfold tailWord_8178056
  simp only [CollatzResearch.WordTrace]
  refine ⟨149139103430153643806441011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198852137906871525075254681 149139103430153643806441011)
  ·
    refine ⟨223708655145230465709661517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149139103430153643806441011 223708655145230465709661517)
    ·
      refine ⟨83890745679461424641123069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223708655145230465709661517 83890745679461424641123069)
      ·
        refine ⟨31459029629798034240421151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83890745679461424641123069 31459029629798034240421151)
        ·
          refine ⟨47188544444697051360631727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31459029629798034240421151 47188544444697051360631727)
          ·
            refine ⟨70782816667045577040947591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47188544444697051360631727 70782816667045577040947591)
            ·
              refine ⟨106174225000568365561421387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70782816667045577040947591 106174225000568365561421387)
              ·
                refine ⟨159261337500852548342132081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106174225000568365561421387 159261337500852548342132081)
                ·
                  refine ⟨119446003125639411256599061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159261337500852548342132081 119446003125639411256599061)
                  ·
                    refine ⟨5599031396514347402653081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119446003125639411256599061 5599031396514347402653081)
                    ·
                      refine ⟨4199273547385760551989811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5599031396514347402653081 4199273547385760551989811)
                      ·
                        rfl

theorem cell23_8178056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_8178056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178056 prefixEnd_8178056 := by exact prefixLift 8178056
  have htrace : WordTrace (prefixWord ++ tailWord_8178056) baseStart_8178056 baseEnd_8178056 := by
    simpa [prefixWord, tailWord_8178056, baseEnd_8178056] using wordTrace_append hprefix tailTrace_8178056
  have hstable : (prefixWord ++ tailWord_8178056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178056).length < 2 ^ (prefixWord ++ tailWord_8178056).sum := by decide
  have hdescent : baseEnd_8178056 < baseStart_8178056 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178069 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_8178069 : Nat := 118140960795 + 8178069 * 2 ^ 59
def prefixEnd_8178069 : Nat := 4983230072969 + 3 ^ 40 * 8178069 * 2
def baseEnd_8178069 : Nat := 4199280222634269001127251

theorem tailTrace_8178069 : CollatzResearch.WordTrace tailWord_8178069 prefixEnd_8178069 4199280222634269001127251 := by
  unfold tailWord_8178069
  simp only [CollatzResearch.WordTrace]
  refine ⟨298278681009260190833105261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198852454006173460555403507 298278681009260190833105261)
  ·
    refine ⟨111854505378472571562414473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298278681009260190833105261 111854505378472571562414473)
    ·
      refine ⟨83890879033854428671810855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111854505378472571562414473 83890879033854428671810855)
      ·
        refine ⟨125836318550781643007716283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83890879033854428671810855 125836318550781643007716283)
        ·
          refine ⟨188754477826172464511574425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125836318550781643007716283 188754477826172464511574425)
          ·
            refine ⟨141565858369629348383680819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188754477826172464511574425 141565858369629348383680819)
            ·
              refine ⟨212348787554444022575521229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141565858369629348383680819 212348787554444022575521229)
              ·
                refine ⟨79630795332916508465820461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212348787554444022575521229 79630795332916508465820461)
                ·
                  refine ⟨29861548249843690674682673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79630795332916508465820461 29861548249843690674682673)
                  ·
                    refine ⟨22396161187382768006012005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29861548249843690674682673 22396161187382768006012005)
                    ·
                      refine ⟨4199280222634269001127251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22396161187382768006012005 4199280222634269001127251)
                      ·
                        rfl

theorem cell23_8178069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_8178069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178069 prefixEnd_8178069 := by exact prefixLift 8178069
  have htrace : WordTrace (prefixWord ++ tailWord_8178069) baseStart_8178069 baseEnd_8178069 := by
    simpa [prefixWord, tailWord_8178069, baseEnd_8178069] using wordTrace_append hprefix tailTrace_8178069
  have hstable : (prefixWord ++ tailWord_8178069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178069).length < 2 ^ (prefixWord ++ tailWord_8178069).sum := by decide
  have hdescent : baseEnd_8178069 < baseStart_8178069 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178129 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 4, 3, 4]
def baseStart_8178129 : Nat := 118140960795 + 8178129 * 2 ^ 59
def prefixEnd_8178129 : Nat := 4983230072969 + 3 ^ 40 * 8178129 * 2
def baseEnd_8178129 : Nat := 4199311031473538766376975

theorem tailTrace_8178129 : CollatzResearch.WordTrace tailWord_8178129 prefixEnd_8178129 4199311031473538766376975 := by
  unfold tailWord_8178129
  simp only [CollatzResearch.WordTrace]
  refine ⟨298280869389042821080289441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198853912926028547386859627 298280869389042821080289441)
  ·
    refine ⟨223710652041782115810217081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298280869389042821080289441 223710652041782115810217081)
    ·
      refine ⟨167782989031336586857662811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223710652041782115810217081 167782989031336586857662811)
      ·
        refine ⟨251674483547004880286494217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167782989031336586857662811 251674483547004880286494217)
        ·
          refine ⟨188755862660253660214870663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251674483547004880286494217 188755862660253660214870663)
          ·
            refine ⟨283133793990380490322305995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188755862660253660214870663 283133793990380490322305995)
            ·
              refine ⟨424700690985570735483458993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283133793990380490322305995 424700690985570735483458993)
              ·
                refine ⟨318525518239178051612594245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424700690985570735483458993 318525518239178051612594245)
                ·
                  refine ⟨59723534669845884677361421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 318525518239178051612594245 59723534669845884677361421)
                  ·
                    refine ⟨22396325501192206754010533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59723534669845884677361421 22396325501192206754010533)
                    ·
                      refine ⟨4199311031473538766376975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22396325501192206754010533 4199311031473538766376975)
                      ·
                        rfl

theorem cell23_8178129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_8178129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178129 prefixEnd_8178129 := by exact prefixLift 8178129
  have htrace : WordTrace (prefixWord ++ tailWord_8178129) baseStart_8178129 baseEnd_8178129 := by
    simpa [prefixWord, tailWord_8178129, baseEnd_8178129] using wordTrace_append hprefix tailTrace_8178129
  have hstable : (prefixWord ++ tailWord_8178129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178129).length < 2 ^ (prefixWord ++ tailWord_8178129).sum := by decide
  have hdescent : baseEnd_8178129 < baseStart_8178129 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178163 : List Nat := [1, 1, 1, 2, 2, 2, 6, 1, 1, 4, 2]
def baseStart_8178163 : Nat := 118140960795 + 8178163 * 2 ^ 59
def prefixEnd_8178163 : Nat := 4983230072969 + 3 ^ 40 * 8178163 * 2
def baseEnd_8178163 : Nat := 4199328489815791633351819

theorem tailTrace_8178163 : CollatzResearch.WordTrace tailWord_8178163 prefixEnd_8178163 4199328489815791633351819 := by
  unfold tailWord_8178163
  simp only [CollatzResearch.WordTrace]
  refine ⟨298282109470919644887027143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198854739647279763258018095 298282109470919644887027143)
  ·
    refine ⟨447423164206379467330540715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298282109470919644887027143 447423164206379467330540715)
    ·
      refine ⟨671134746309569200995811073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447423164206379467330540715 671134746309569200995811073)
      ·
        refine ⟨503351059732176900746858305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 671134746309569200995811073 503351059732176900746858305)
        ·
          refine ⟨377513294799132675560143729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503351059732176900746858305 377513294799132675560143729)
          ·
            refine ⟨283134971099349506670107797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377513294799132675560143729 283134971099349506670107797)
            ·
              refine ⟨13271951770282008125161303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 283134971099349506670107797 13271951770282008125161303)
              ·
                refine ⟨19907927655423012187741955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13271951770282008125161303 19907927655423012187741955)
                ·
                  refine ⟨29861891483134518281612933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19907927655423012187741955 29861891483134518281612933)
                  ·
                    refine ⟨5599104653087722177802425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29861891483134518281612933 5599104653087722177802425)
                    ·
                      refine ⟨4199328489815791633351819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5599104653087722177802425 4199328489815791633351819)
                      ·
                        rfl

theorem cell23_8178163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 4, 2].length) (baseStart_8178163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178163 prefixEnd_8178163 := by exact prefixLift 8178163
  have htrace : WordTrace (prefixWord ++ tailWord_8178163) baseStart_8178163 baseEnd_8178163 := by
    simpa [prefixWord, tailWord_8178163, baseEnd_8178163] using wordTrace_append hprefix tailTrace_8178163
  have hstable : (prefixWord ++ tailWord_8178163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178163).length < 2 ^ (prefixWord ++ tailWord_8178163).sum := by decide
  have hdescent : baseEnd_8178163 < baseStart_8178163 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178169 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 9]
def baseStart_8178169 : Nat := 118140960795 + 8178169 * 2 ^ 59
def prefixEnd_8178169 : Nat := 4983230072969 + 3 ^ 40 * 8178169 * 2
def baseEnd_8178169 : Nat := 466592396744413178875199

theorem tailTrace_8178169 : CollatzResearch.WordTrace tailWord_8178169 prefixEnd_8178169 466592396744413178875199 := by
  unfold tailWord_8178169
  simp only [CollatzResearch.WordTrace]
  refine ⟨298282328308897907911745561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198854885539265271941163707 298282328308897907911745561)
  ·
    refine ⟨223711746231673430933809171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298282328308897907911745561 223711746231673430933809171)
    ·
      refine ⟨335567619347510146400713757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223711746231673430933809171 335567619347510146400713757)
      ·
        refine ⟨125837857255316304900267659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335567619347510146400713757 125837857255316304900267659)
        ·
          refine ⟨188756785882974457350401489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125837857255316304900267659 188756785882974457350401489)
          ·
            refine ⟨141567589412230843012801117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188756785882974457350401489 141567589412230843012801117)
            ·
              refine ⟨53087846029586566129800419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141567589412230843012801117 53087846029586566129800419)
              ·
                refine ⟨79631769044379849194700629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53087846029586566129800419 79631769044379849194700629)
                ·
                  refine ⟨466592396744413178875199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79631769044379849194700629 466592396744413178875199)
                  ·
                    rfl

theorem cell23_8178169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 9].length) (baseStart_8178169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178169 prefixEnd_8178169 := by exact prefixLift 8178169
  have htrace : WordTrace (prefixWord ++ tailWord_8178169) baseStart_8178169 baseEnd_8178169 := by
    simpa [prefixWord, tailWord_8178169, baseEnd_8178169] using wordTrace_append hprefix tailTrace_8178169
  have hstable : (prefixWord ++ tailWord_8178169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178169).length < 2 ^ (prefixWord ++ tailWord_8178169).sum := by decide
  have hdescent : baseEnd_8178169 < baseStart_8178169 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178180 : List Nat := [2, 3, 2, 3, 1, 1, 2, 2, 1, 4, 2]
def baseStart_8178180 : Nat := 118140960795 + 8178180 * 2 ^ 59
def prefixEnd_8178180 : Nat := 4983230072969 + 3 ^ 40 * 8178180 * 2
def baseEnd_8178180 : Nat := 4199337218986918066839241

theorem tailTrace_8178180 : CollatzResearch.WordTrace tailWord_8178180 prefixEnd_8178180 4199337218986918066839241 := by
  unfold tailWord_8178180
  simp only [CollatzResearch.WordTrace]
  refine ⟨149141364755929028395197997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198855153007905371193597329 149141364755929028395197997)
  ·
    refine ⟨55928011783473385648199249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149141364755929028395197997 55928011783473385648199249)
    ·
      refine ⟨41946008837605039236149437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55928011783473385648199249 41946008837605039236149437)
      ·
        refine ⟨15729753314101889713556039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41946008837605039236149437 15729753314101889713556039)
        ·
          refine ⟨23594629971152834570334059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15729753314101889713556039 23594629971152834570334059)
          ·
            refine ⟨35391944956729251855501089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23594629971152834570334059 35391944956729251855501089)
            ·
              refine ⟨26543958717546938891625817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35391944956729251855501089 26543958717546938891625817)
              ·
                refine ⟨19907969038160204168719363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26543958717546938891625817 19907969038160204168719363)
                ·
                  refine ⟨29861953557240306253079045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19907969038160204168719363 29861953557240306253079045)
                  ·
                    refine ⟨5599116291982557422452321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29861953557240306253079045 5599116291982557422452321)
                    ·
                      refine ⟨4199337218986918066839241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5599116291982557422452321 4199337218986918066839241)
                      ·
                        rfl

theorem cell23_8178180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_8178180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178180 prefixEnd_8178180 := by exact prefixLift 8178180
  have htrace : WordTrace (prefixWord ++ tailWord_8178180) baseStart_8178180 baseEnd_8178180 := by
    simpa [prefixWord, tailWord_8178180, baseEnd_8178180] using wordTrace_append hprefix tailTrace_8178180
  have hstable : (prefixWord ++ tailWord_8178180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178180).length < 2 ^ (prefixWord ++ tailWord_8178180).sum := by decide
  have hdescent : baseEnd_8178180 < baseStart_8178180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178256 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 3]
def baseStart_8178256 : Nat := 118140960795 + 8178256 * 2 ^ 59
def prefixEnd_8178256 : Nat := 4983230072969 + 3 ^ 40 * 8178256 * 2
def baseEnd_8178256 : Nat := 4199376243516659769488891

theorem tailTrace_8178256 : CollatzResearch.WordTrace tailWord_8178256 prefixEnd_8178256 4199376243516659769488891 := by
  unfold tailWord_8178256
  simp only [CollatzResearch.WordTrace]
  refine ⟨149142750729791360885081311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198857000973055147846775081 149142750729791360885081311)
  ·
    refine ⟨223714126094687041327621967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149142750729791360885081311 223714126094687041327621967)
    ·
      refine ⟨335571189142030561991432951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223714126094687041327621967 335571189142030561991432951)
      ·
        refine ⟨503356783713045842987149427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335571189142030561991432951 503356783713045842987149427)
        ·
          refine ⟨755035175569568764480724141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503356783713045842987149427 755035175569568764480724141)
          ·
            refine ⟨283138190838588286680271553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 755035175569568764480724141 283138190838588286680271553)
            ·
              refine ⟨212353643128941215010203665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283138190838588286680271553 212353643128941215010203665)
              ·
                refine ⟨159265232346705911257652749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212353643128941215010203665 159265232346705911257652749)
                ·
                  refine ⟨59724462130014716721619781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159265232346705911257652749 59724462130014716721619781)
                  ·
                    refine ⟨11198336649377759385303709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59724462130014716721619781 11198336649377759385303709)
                    ·
                      refine ⟨4199376243516659769488891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11198336649377759385303709 4199376243516659769488891)
                      ·
                        rfl

theorem cell23_8178256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 3].length) (baseStart_8178256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178256 prefixEnd_8178256 := by exact prefixLift 8178256
  have htrace : WordTrace (prefixWord ++ tailWord_8178256) baseStart_8178256 baseEnd_8178256 := by
    simpa [prefixWord, tailWord_8178256, baseEnd_8178256] using wordTrace_append hprefix tailTrace_8178256
  have hstable : (prefixWord ++ tailWord_8178256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178256).length < 2 ^ (prefixWord ++ tailWord_8178256).sum := by decide
  have hdescent : baseEnd_8178256 < baseStart_8178256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178303 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 7, 1, 3]
def baseStart_8178303 : Nat := 118140960795 + 8178303 * 2 ^ 59
def prefixEnd_8178303 : Nat := 4983230072969 + 3 ^ 40 * 8178303 * 2
def baseEnd_8178303 : Nat := 4199400377107421085601175

theorem tailTrace_8178303 : CollatzResearch.WordTrace tailWord_8178303 prefixEnd_8178303 4199400377107421085601175 := by
  unfold tailWord_8178303
  simp only [CollatzResearch.WordTrace]
  refine ⟨298287215690412448797123563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198858143793608299198082375 298287215690412448797123563)
  ·
    refine ⟨447430823535618673195685345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298287215690412448797123563 447430823535618673195685345)
    ·
      refine ⟨335573117651714004896764009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447430823535618673195685345 335573117651714004896764009)
      ·
        refine ⟨251679838238785503672573007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335573117651714004896764009 251679838238785503672573007)
        ·
          refine ⟨377519757358178255508859511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251679838238785503672573007 377519757358178255508859511)
          ·
            refine ⟨566279636037267383263289267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377519757358178255508859511 566279636037267383263289267)
            ·
              refine ⟨849419454055901074894933901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566279636037267383263289267 849419454055901074894933901)
              ·
                refine ⟨318532295270962903085600213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 849419454055901074894933901 318532295270962903085600213)
                ·
                  refine ⟨7465600670413193041068755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 318532295270962903085600213 7465600670413193041068755)
                  ·
                    refine ⟨11198401005619789561603133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7465600670413193041068755 11198401005619789561603133)
                    ·
                      refine ⟨4199400377107421085601175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11198401005619789561603133 4199400377107421085601175)
                      ·
                        rfl

theorem cell23_8178303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 1, 3].length) (baseStart_8178303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178303 prefixEnd_8178303 := by exact prefixLift 8178303
  have htrace : WordTrace (prefixWord ++ tailWord_8178303) baseStart_8178303 baseEnd_8178303 := by
    simpa [prefixWord, tailWord_8178303, baseEnd_8178303] using wordTrace_append hprefix tailTrace_8178303
  have hstable : (prefixWord ++ tailWord_8178303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178303).length < 2 ^ (prefixWord ++ tailWord_8178303).sum := by decide
  have hdescent : baseEnd_8178303 < baseStart_8178303 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178313 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 3, 5, 2]
def baseStart_8178313 : Nat := 118140960795 + 8178313 * 2 ^ 59
def prefixEnd_8178313 : Nat := 4983230072969 + 3 ^ 40 * 8178313 * 2
def baseEnd_8178313 : Nat := 4199405511913966046476129

theorem tailTrace_8178313 : CollatzResearch.WordTrace tailWord_8178313 prefixEnd_8178313 4199405511913966046476129 := by
  unfold tailWord_8178313
  simp only [CollatzResearch.WordTrace]
  refine ⟨298287580420376220504987593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198858386946917480336658395 298287580420376220504987593)
  ·
    refine ⟨223715685315282165378740695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298287580420376220504987593 223715685315282165378740695)
    ·
      refine ⟨335573527972923248068111043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223715685315282165378740695 335573527972923248068111043)
      ·
        refine ⟨503360291959384872102166565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335573527972923248068111043 503360291959384872102166565)
        ·
          refine ⟨94380054742384663519156231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 503360291959384872102166565 94380054742384663519156231)
          ·
            refine ⟨141570082113576995278734347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94380054742384663519156231 141570082113576995278734347)
            ·
              refine ⟨212355123170365492918101521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141570082113576995278734347 212355123170365492918101521)
              ·
                refine ⟨159266342377774119688576141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212355123170365492918101521 159266342377774119688576141)
                ·
                  refine ⟨59724878391665294883216053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159266342377774119688576141 59724878391665294883216053)
                  ·
                    refine ⟨5599207349218621395301505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59724878391665294883216053 5599207349218621395301505)
                    ·
                      refine ⟨4199405511913966046476129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5599207349218621395301505 4199405511913966046476129)
                      ·
                        rfl

theorem cell23_8178313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 5, 2].length) (baseStart_8178313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178313 prefixEnd_8178313 := by exact prefixLift 8178313
  have htrace : WordTrace (prefixWord ++ tailWord_8178313) baseStart_8178313 baseEnd_8178313 := by
    simpa [prefixWord, tailWord_8178313, baseEnd_8178313] using wordTrace_append hprefix tailTrace_8178313
  have hstable : (prefixWord ++ tailWord_8178313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178313).length < 2 ^ (prefixWord ++ tailWord_8178313).sum := by decide
  have hdescent : baseEnd_8178313 < baseStart_8178313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178337 : List Nat := [1, 2, 3, 3, 3, 1, 1, 2, 3, 1, 3]
def baseStart_8178337 : Nat := 118140960795 + 8178337 * 2 ^ 59
def prefixEnd_8178337 : Nat := 4983230072969 + 3 ^ 40 * 8178337 * 2
def baseEnd_8178337 : Nat := 4199417835449673952576019

theorem tailTrace_8178337 : CollatzResearch.WordTrace tailWord_8178337 prefixEnd_8178337 4199417835449673952576019 := by
  unfold tailWord_8178337
  simp only [CollatzResearch.WordTrace]
  refine ⟨298288455772289272603861265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198858970514859515069240843 298288455772289272603861265)
  ·
    refine ⟨223716341829216954452895949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298288455772289272603861265 223716341829216954452895949)
    ·
      refine ⟨83893628185956357919835981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223716341829216954452895949 83893628185956357919835981)
      ·
        refine ⟨31460110569733634219938493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83893628185956357919835981 31460110569733634219938493)
        ·
          refine ⟨11797541463650112832476935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31460110569733634219938493 11797541463650112832476935)
          ·
            refine ⟨17696312195475169248715403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11797541463650112832476935 17696312195475169248715403)
            ·
              refine ⟨26544468293212753873073105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17696312195475169248715403 26544468293212753873073105)
              ·
                refine ⟨19908351219909565404804829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26544468293212753873073105 19908351219909565404804829)
                ·
                  refine ⟨7465631707466087026801811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19908351219909565404804829 7465631707466087026801811)
                  ·
                    refine ⟨11198447561199130540202717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7465631707466087026801811 11198447561199130540202717)
                    ·
                      refine ⟨4199417835449673952576019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11198447561199130540202717 4199417835449673952576019)
                      ·
                        rfl

theorem cell23_8178337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_8178337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178337 prefixEnd_8178337 := by exact prefixLift 8178337
  have htrace : WordTrace (prefixWord ++ tailWord_8178337) baseStart_8178337 baseEnd_8178337 := by
    simpa [prefixWord, tailWord_8178337, baseEnd_8178337] using wordTrace_append hprefix tailTrace_8178337
  have hstable : (prefixWord ++ tailWord_8178337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178337).length < 2 ^ (prefixWord ++ tailWord_8178337).sum := by decide
  have hdescent : baseEnd_8178337 < baseStart_8178337 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178357 : List Nat := [1, 3, 3, 3, 1, 1, 4, 1, 1, 5]
def baseStart_8178357 : Nat := 118140960795 + 8178357 * 2 ^ 59
def prefixEnd_8178357 : Nat := 4983230072969 + 3 ^ 40 * 8178357 * 2
def baseEnd_8178357 : Nat := 1399809368354254624775309

theorem tailTrace_8178357 : CollatzResearch.WordTrace tailWord_8178357 prefixEnd_8178357 1399809368354254624775309 := by
  unfold tailWord_8178357
  simp only [CollatzResearch.WordTrace]
  refine ⟨298289185232216816019589325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198859456821477877346392883 298289185232216816019589325)
  ·
    refine ⟨111858444462081306007345997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298289185232216816019589325 111858444462081306007345997)
    ·
      refine ⟨41946916673280489752754749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111858444462081306007345997 41946916673280489752754749)
      ·
        refine ⟨15730093752480183657283031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41946916673280489752754749 15730093752480183657283031)
        ·
          refine ⟨23595140628720275485924547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15730093752480183657283031 23595140628720275485924547)
          ·
            refine ⟨35392710943080413228886821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23595140628720275485924547 35392710943080413228886821)
            ·
              refine ⟨6636133301827577480416279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35392710943080413228886821 6636133301827577480416279)
              ·
                refine ⟨9954199952741366220624419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6636133301827577480416279 9954199952741366220624419)
                ·
                  refine ⟨14931299929112049330936629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9954199952741366220624419 14931299929112049330936629)
                  ·
                    refine ⟨1399809368354254624775309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14931299929112049330936629 1399809368354254624775309)
                    ·
                      rfl

theorem cell23_8178357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_8178357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178357 prefixEnd_8178357 := by exact prefixLift 8178357
  have htrace : WordTrace (prefixWord ++ tailWord_8178357) baseStart_8178357 baseEnd_8178357 := by
    simpa [prefixWord, tailWord_8178357, baseEnd_8178357] using wordTrace_append hprefix tailTrace_8178357
  have hstable : (prefixWord ++ tailWord_8178357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178357).length < 2 ^ (prefixWord ++ tailWord_8178357).sum := by decide
  have hdescent : baseEnd_8178357 < baseStart_8178357 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178380 : List Nat := [2, 2, 1, 5, 1, 2, 1, 2, 1, 1, 5]
def baseStart_8178380 : Nat := 118140960795 + 8178380 * 2 ^ 59
def prefixEnd_8178380 : Nat := 4983230072969 + 3 ^ 40 * 8178380 * 2
def baseEnd_8178380 : Nat := 4199439915117817284338321

theorem tailTrace_8178380 : CollatzResearch.WordTrace tailWord_8178380 prefixEnd_8178380 4199439915117817284338321 := by
  unfold tailWord_8178380
  simp only [CollatzResearch.WordTrace]
  refine ⟨149145012055566745473838297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198860016074088993965117729 149145012055566745473838297)
  ·
    refine ⟨111858759041675059105378723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149145012055566745473838297 111858759041675059105378723)
    ·
      refine ⟨167788138562512588658068085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111858759041675059105378723 167788138562512588658068085)
      ·
        refine ⟨15730137990235555186693883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167788138562512588658068085 15730137990235555186693883)
        ·
          refine ⟨23595206985353332780040825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15730137990235555186693883 23595206985353332780040825)
          ·
            refine ⟨17696405239014999585030619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23595206985353332780040825 17696405239014999585030619)
            ·
              refine ⟨26544607858522499377545929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17696405239014999585030619 26544607858522499377545929)
              ·
                refine ⟨19908455893891874533159447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26544607858522499377545929 19908455893891874533159447)
                ·
                  refine ⟨29862683840837811799739171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19908455893891874533159447 29862683840837811799739171)
                  ·
                    refine ⟨44794025761256717699608757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29862683840837811799739171 44794025761256717699608757)
                    ·
                      refine ⟨4199439915117817284338321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44794025761256717699608757 4199439915117817284338321)
                      ·
                        rfl

theorem cell23_8178380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_8178380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178380 prefixEnd_8178380 := by exact prefixLift 8178380
  have htrace : WordTrace (prefixWord ++ tailWord_8178380) baseStart_8178380 baseEnd_8178380 := by
    simpa [prefixWord, tailWord_8178380, baseEnd_8178380] using wordTrace_append hprefix tailTrace_8178380
  have hstable : (prefixWord ++ tailWord_8178380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178380).length < 2 ^ (prefixWord ++ tailWord_8178380).sum := by decide
  have hdescent : baseEnd_8178380 < baseStart_8178380 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178433 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_8178433 : Nat := 118140960795 + 8178433 * 2 ^ 59
def prefixEnd_8178433 : Nat := 4983230072969 + 3 ^ 40 * 8178433 * 2
def baseEnd_8178433 : Nat := 4199467129592505576975577

theorem tailTrace_8178433 : CollatzResearch.WordTrace tailWord_8178433 prefixEnd_8178433 4199467129592505576975577 := by
  unfold tailWord_8178433
  simp only [CollatzResearch.WordTrace]
  refine ⟨298291957179941480999355953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198861304786627653999570635 298291957179941480999355953)
  ·
    refine ⟨223718967884956110749516965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298291957179941480999355953 223718967884956110749516965)
    ·
      refine ⟨41947306478429270765534431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223718967884956110749516965 41947306478429270765534431)
      ·
        refine ⟨62920959717643906148301647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41947306478429270765534431 62920959717643906148301647)
        ·
          refine ⟨94381439576465859222452471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62920959717643906148301647 94381439576465859222452471)
          ·
            refine ⟨141572159364698788833678707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94381439576465859222452471 141572159364698788833678707)
            ·
              refine ⟨212358239047048183250518061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141572159364698788833678707 212358239047048183250518061)
              ·
                refine ⟨79634339642643068718944273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212358239047048183250518061 79634339642643068718944273)
                ·
                  refine ⟨59725754731982301539208205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79634339642643068718944273 59725754731982301539208205)
                  ·
                    refine ⟨22397158024493363077203077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59725754731982301539208205 22397158024493363077203077)
                    ·
                      refine ⟨4199467129592505576975577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22397158024493363077203077 4199467129592505576975577)
                      ·
                        rfl

theorem cell23_8178433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_8178433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178433 prefixEnd_8178433 := by exact prefixLift 8178433
  have htrace : WordTrace (prefixWord ++ tailWord_8178433) baseStart_8178433 baseEnd_8178433 := by
    simpa [prefixWord, tailWord_8178433, baseEnd_8178433] using wordTrace_append hprefix tailTrace_8178433
  have hstable : (prefixWord ++ tailWord_8178433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178433).length < 2 ^ (prefixWord ++ tailWord_8178433).sum := by decide
  have hdescent : baseEnd_8178433 < baseStart_8178433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178453 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_8178453 : Nat := 118140960795 + 8178453 * 2 ^ 59
def prefixEnd_8178453 : Nat := 4983230072969 + 3 ^ 40 * 8178453 * 2
def baseEnd_8178453 : Nat := 4199477399205595498725485

theorem tailTrace_8178453 : CollatzResearch.WordTrace tailWord_8178453 prefixEnd_8178453 4199477399205595498725485 := by
  unfold tailWord_8178453
  simp only [CollatzResearch.WordTrace]
  refine ⟨298292686639869024415084013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198861791093246016276722675 298292686639869024415084013)
  ·
    refine ⟨111859757489950884155656505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298292686639869024415084013 111859757489950884155656505)
    ·
      refine ⟨83894818117463163116742379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111859757489950884155656505 83894818117463163116742379)
      ·
        refine ⟨125842227176194744675113569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83894818117463163116742379 125842227176194744675113569)
        ·
          refine ⟨94381670382146058506335177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125842227176194744675113569 94381670382146058506335177)
          ·
            refine ⟨70786252786609543879751383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94381670382146058506335177 70786252786609543879751383)
            ·
              refine ⟨106179379179914315819627075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70786252786609543879751383 106179379179914315819627075)
              ·
                refine ⟨159269068769871473729440613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106179379179914315819627075 159269068769871473729440613)
                ·
                  refine ⟨29862950394350901324270115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159269068769871473729440613 29862950394350901324270115)
                  ·
                    refine ⟨44794425591526351986405173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29862950394350901324270115 44794425591526351986405173)
                    ·
                      refine ⟨4199477399205595498725485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44794425591526351986405173 4199477399205595498725485)
                      ·
                        rfl

theorem cell23_8178453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_8178453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178453 prefixEnd_8178453 := by exact prefixLift 8178453
  have htrace : WordTrace (prefixWord ++ tailWord_8178453) baseStart_8178453 baseEnd_8178453 := by
    simpa [prefixWord, tailWord_8178453, baseEnd_8178453] using wordTrace_append hprefix tailTrace_8178453
  have hstable : (prefixWord ++ tailWord_8178453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178453).length < 2 ^ (prefixWord ++ tailWord_8178453).sum := by decide
  have hdescent : baseEnd_8178453 < baseStart_8178453 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178503 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 1, 7]
def baseStart_8178503 : Nat := 118140960795 + 8178503 * 2 ^ 59
def prefixEnd_8178503 : Nat := 4983230072969 + 3 ^ 40 * 8178503 * 2
def baseEnd_8178503 : Nat := 1399834357746106767700085

theorem tailTrace_8178503 : CollatzResearch.WordTrace tailWord_8178503 prefixEnd_8178503 1399834357746106767700085 := by
  unfold tailWord_8178503
  simp only [CollatzResearch.WordTrace]
  refine ⟨298294510289687882954404163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198863006859791921969602775 298294510289687882954404163)
  ·
    refine ⟨447441765434531824431606245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298294510289687882954404163 447441765434531824431606245)
    ·
      refine ⟨83895331018974717080926171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447441765434531824431606245 83895331018974717080926171)
      ·
        refine ⟨125842996528462075621389257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83895331018974717080926171 125842996528462075621389257)
        ·
          refine ⟨94382247396346556716041943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125842996528462075621389257 94382247396346556716041943)
          ·
            refine ⟨141573371094519835074062915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94382247396346556716041943 141573371094519835074062915)
            ·
              refine ⟨212360056641779752611094373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141573371094519835074062915 212360056641779752611094373)
              ·
                refine ⟨39817510620333703614580195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212360056641779752611094373 39817510620333703614580195)
                ·
                  refine ⟨59726265930500555421870293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39817510620333703614580195 59726265930500555421870293)
                  ·
                    refine ⟨1399834357746106767700085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59726265930500555421870293 1399834357746106767700085)
                    ·
                      rfl

theorem cell23_8178503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_8178503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178503 prefixEnd_8178503 := by exact prefixLift 8178503
  have htrace : WordTrace (prefixWord ++ tailWord_8178503) baseStart_8178503 baseEnd_8178503 := by
    simpa [prefixWord, tailWord_8178503, baseEnd_8178503] using wordTrace_append hprefix tailTrace_8178503
  have hstable : (prefixWord ++ tailWord_8178503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178503).length < 2 ^ (prefixWord ++ tailWord_8178503).sum := by decide
  have hdescent : baseEnd_8178503 < baseStart_8178503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178524 : List Nat := [2, 2, 4, 2, 1, 2, 2, 3, 5]
def baseStart_8178524 : Nat := 118140960795 + 8178524 * 2 ^ 59
def prefixEnd_8178524 : Nat := 4983230072969 + 3 ^ 40 * 8178524 * 2
def baseEnd_8178524 : Nat := 466612650703562746770851

theorem tailTrace_8178524 : CollatzResearch.WordTrace tailWord_8178524 prefixEnd_8178524 466612650703562746770851 := by
  unfold tailWord_8178524
  simp only [CollatzResearch.WordTrace]
  refine ⟨149147638111305901770459313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198863517481741202360612417 149147638111305901770459313)
  ·
    refine ⟨111860728583479426327844485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149147638111305901770459313 111860728583479426327844485)
    ·
      refine ⟨20973886609402392436470841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111860728583479426327844485 20973886609402392436470841)
      ·
        refine ⟨15730414957051794327353131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20973886609402392436470841 15730414957051794327353131)
        ·
          refine ⟨23595622435577691491029697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15730414957051794327353131 23595622435577691491029697)
          ·
            refine ⟨17696716826683268618272273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23595622435577691491029697 17696716826683268618272273)
            ·
              refine ⟨13272537620012451463704205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17696716826683268618272273 13272537620012451463704205)
              ·
                refine ⟨4977201607504669298889077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13272537620012451463704205 4977201607504669298889077)
                ·
                  refine ⟨466612650703562746770851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4977201607504669298889077 466612650703562746770851)
                  ·
                    rfl

theorem cell23_8178524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 5].length) (baseStart_8178524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178524 prefixEnd_8178524 := by exact prefixLift 8178524
  have htrace : WordTrace (prefixWord ++ tailWord_8178524) baseStart_8178524 baseEnd_8178524 := by
    simpa [prefixWord, tailWord_8178524, baseEnd_8178524] using wordTrace_append hprefix tailTrace_8178524
  have hstable : (prefixWord ++ tailWord_8178524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178524).length < 2 ^ (prefixWord ++ tailWord_8178524).sum := by decide
  have hdescent : baseEnd_8178524 < baseStart_8178524 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178540 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 4]
def baseStart_8178540 : Nat := 118140960795 + 8178540 * 2 ^ 59
def prefixEnd_8178540 : Nat := 4983230072969 + 3 ^ 40 * 8178540 * 2
def baseEnd_8178540 : Nat := 4199522072022536658337585

theorem tailTrace_8178540 : CollatzResearch.WordTrace tailWord_8178540 prefixEnd_8178540 4199522072022536658337585 := by
  unfold tailWord_8178540
  simp only [CollatzResearch.WordTrace]
  refine ⟨149147929895276919136750537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198863906527035892182334049 149147929895276919136750537)
  ·
    refine ⟨111860947421457689352562903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149147929895276919136750537 111860947421457689352562903)
    ·
      refine ⟨167791421132186534028844355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111860947421457689352562903 167791421132186534028844355)
      ·
        refine ⟨251687131698279801043266533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167791421132186534028844355 251687131698279801043266533)
        ·
          refine ⟨47191337193427462695612475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251687131698279801043266533 47191337193427462695612475)
          ·
            refine ⟨70787005790141194043418713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47191337193427462695612475 70787005790141194043418713)
            ·
              refine ⟨53090254342605895532564035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70787005790141194043418713 53090254342605895532564035)
              ·
                refine ⟨79635381513908843298846053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53090254342605895532564035 79635381513908843298846053)
                ·
                  refine ⟨14931634033857908118533635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79635381513908843298846053 14931634033857908118533635)
                  ·
                    refine ⟨22397451050786862177800453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14931634033857908118533635 22397451050786862177800453)
                    ·
                      refine ⟨4199522072022536658337585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22397451050786862177800453 4199522072022536658337585)
                      ·
                        rfl

theorem cell23_8178540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_8178540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178540 prefixEnd_8178540 := by exact prefixLift 8178540
  have htrace : WordTrace (prefixWord ++ tailWord_8178540) baseStart_8178540 baseEnd_8178540 := by
    simpa [prefixWord, tailWord_8178540, baseEnd_8178540] using wordTrace_append hprefix tailTrace_8178540
  have hstable : (prefixWord ++ tailWord_8178540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178540).length < 2 ^ (prefixWord ++ tailWord_8178540).sum := by decide
  have hdescent : baseEnd_8178540 < baseStart_8178540 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178543 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 5]
def baseStart_8178543 : Nat := 118140960795 + 8178543 * 2 ^ 59
def prefixEnd_8178543 : Nat := 4983230072969 + 3 ^ 40 * 8178543 * 2
def baseEnd_8178543 : Nat := 4199523612464500146600071

theorem tailTrace_8178543 : CollatzResearch.WordTrace tailWord_8178543 prefixEnd_8178543 4199523612464500146600071 := by
  unfold tailWord_8178543
  simp only [CollatzResearch.WordTrace]
  refine ⟨298295969209542969785860283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198863979473028646523906855 298295969209542969785860283)
  ·
    refine ⟨447443953814314454678790425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298295969209542969785860283 447443953814314454678790425)
    ·
      refine ⟨335582965360735841009092819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447443953814314454678790425 335582965360735841009092819)
      ·
        refine ⟨503374448041103761513639229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335582965360735841009092819 503374448041103761513639229)
        ·
          refine ⟨188765418015413910567614711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 503374448041103761513639229 188765418015413910567614711)
          ·
            refine ⟨283148127023120865851422067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188765418015413910567614711 283148127023120865851422067)
            ·
              refine ⟨424722190534681298777133101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283148127023120865851422067 424722190534681298777133101)
              ·
                refine ⟨159270821450505487041424913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 424722190534681298777133101 159270821450505487041424913)
                ·
                  refine ⟨119453116087879115281068685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159270821450505487041424913 119453116087879115281068685)
                  ·
                    refine ⟨44794918532954668230400757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119453116087879115281068685 44794918532954668230400757)
                    ·
                      refine ⟨4199523612464500146600071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44794918532954668230400757 4199523612464500146600071)
                      ·
                        rfl

theorem cell23_8178543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_8178543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178543 prefixEnd_8178543 := by exact prefixLift 8178543
  have htrace : WordTrace (prefixWord ++ tailWord_8178543) baseStart_8178543 baseEnd_8178543 := by
    simpa [prefixWord, tailWord_8178543, baseEnd_8178543] using wordTrace_append hprefix tailTrace_8178543
  have hstable : (prefixWord ++ tailWord_8178543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178543).length < 2 ^ (prefixWord ++ tailWord_8178543).sum := by decide
  have hdescent : baseEnd_8178543 < baseStart_8178543 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178557 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 2, 4, 2]
def baseStart_8178557 : Nat := 118140960795 + 8178557 * 2 ^ 59
def prefixEnd_8178557 : Nat := 4983230072969 + 3 ^ 40 * 8178557 * 2
def baseEnd_8178557 : Nat := 4199530801193663091825007

theorem tailTrace_8178557 : CollatzResearch.WordTrace tailWord_8178557 prefixEnd_8178557 4199530801193663091825007 := by
  unfold tailWord_8178557
  simp only [CollatzResearch.WordTrace]
  refine ⟨298296479831492250176869925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198864319887661500117913283 298296479831492250176869925)
  ·
    refine ⟨55930589968404796908163111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298296479831492250176869925 55930589968404796908163111)
    ·
      refine ⟨83895884952607195362244667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55930589968404796908163111 83895884952607195362244667)
      ·
        refine ⟨125843827428910793043367001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83895884952607195362244667 125843827428910793043367001)
        ·
          refine ⟨94382870571683094782525251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125843827428910793043367001 94382870571683094782525251)
          ·
            refine ⟨141574305857524642173787877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94382870571683094782525251 141574305857524642173787877)
            ·
              refine ⟨26545182348285870407585227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141574305857524642173787877 26545182348285870407585227)
              ·
                refine ⟨39817773522428805611377841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26545182348285870407585227 39817773522428805611377841)
                ·
                  refine ⟨29863330141821604208533381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39817773522428805611377841 29863330141821604208533381)
                  ·
                    refine ⟨5599374401591550789100009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29863330141821604208533381 5599374401591550789100009)
                    ·
                      refine ⟨4199530801193663091825007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5599374401591550789100009 4199530801193663091825007)
                      ·
                        rfl

theorem cell23_8178557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_8178557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178557 prefixEnd_8178557 := by exact prefixLift 8178557
  have htrace : WordTrace (prefixWord ++ tailWord_8178557) baseStart_8178557 baseEnd_8178557 := by
    simpa [prefixWord, tailWord_8178557, baseEnd_8178557] using wordTrace_append hprefix tailTrace_8178557
  have hstable : (prefixWord ++ tailWord_8178557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178557).length < 2 ^ (prefixWord ++ tailWord_8178557).sum := by decide
  have hdescent : baseEnd_8178557 < baseStart_8178557 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178560 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 3]
def baseStart_8178560 : Nat := 118140960795 + 8178560 * 2 ^ 59
def prefixEnd_8178560 : Nat := 4983230072969 + 3 ^ 40 * 8178560 * 2
def baseEnd_8178560 : Nat := 4199532341635626580087493

theorem tailTrace_8178560 : CollatzResearch.WordTrace tailWord_8178560 prefixEnd_8178560 4199532341635626580087493 := by
  unfold tailWord_8178560
  simp only [CollatzResearch.WordTrace]
  refine ⟨149148294625240690844614567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198864392833654254459486089 149148294625240690844614567)
  ·
    refine ⟨223722441937861036266921851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149148294625240690844614567 223722441937861036266921851)
    ·
      refine ⟨335583662906791554400382777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223722441937861036266921851 335583662906791554400382777)
      ·
        refine ⟨251687747180093665800287083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335583662906791554400382777 251687747180093665800287083)
        ·
          refine ⟨377531620770140498700430625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251687747180093665800287083 377531620770140498700430625)
          ·
            refine ⟨283148715577605374025322969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377531620770140498700430625 283148715577605374025322969)
            ·
              refine ⟨212361536683204030518992227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283148715577605374025322969 212361536683204030518992227)
              ·
                refine ⟨318542305024806045778488341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212361536683204030518992227 318542305024806045778488341)
                ·
                  refine ⟨14931670548037783395866641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 318542305024806045778488341 14931670548037783395866641)
                  ·
                    refine ⟨11198752911028337546899981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14931670548037783395866641 11198752911028337546899981)
                    ·
                      refine ⟨4199532341635626580087493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11198752911028337546899981 4199532341635626580087493)
                      ·
                        rfl

theorem cell23_8178560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_8178560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178560 prefixEnd_8178560 := by exact prefixLift 8178560
  have htrace : WordTrace (prefixWord ++ tailWord_8178560) baseStart_8178560 baseEnd_8178560 := by
    simpa [prefixWord, tailWord_8178560, baseEnd_8178560] using wordTrace_append hprefix tailTrace_8178560
  have hstable : (prefixWord ++ tailWord_8178560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178560).length < 2 ^ (prefixWord ++ tailWord_8178560).sum := by decide
  have hdescent : baseEnd_8178560 < baseStart_8178560 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178567 : List Nat := [1, 1, 4, 2, 3, 1, 2, 2, 3, 4]
def baseStart_8178567 : Nat := 118140960795 + 8178567 * 2 ^ 59
def prefixEnd_8178567 : Nat := 4983230072969 + 3 ^ 40 * 8178567 * 2
def baseEnd_8178567 : Nat := 1399845312000069350899987

theorem tailTrace_8178567 : CollatzResearch.WordTrace tailWord_8178567 prefixEnd_8178567 1399845312000069350899987 := by
  unfold tailWord_8178567
  simp only [CollatzResearch.WordTrace]
  refine ⟨298296844561456021884733955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198864563040970681256489303 298296844561456021884733955)
  ·
    refine ⟨447445266842184032827100933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298296844561456021884733955 447445266842184032827100933)
    ·
      refine ⟨83895987532909506155081425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447445266842184032827100933 83895987532909506155081425)
      ·
        refine ⟨62921990649682129616311069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83895987532909506155081425 62921990649682129616311069)
        ·
          refine ⟨23595746493630798606116651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62921990649682129616311069 23595746493630798606116651)
          ·
            refine ⟨35393619740446197909174977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23595746493630798606116651 35393619740446197909174977)
            ·
              refine ⟨26545214805334648431881233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35393619740446197909174977 26545214805334648431881233)
              ·
                refine ⟨19908911104000986323910925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26545214805334648431881233 19908911104000986323910925)
                ·
                  refine ⟨7465841664000369871466597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19908911104000986323910925 7465841664000369871466597)
                  ·
                    refine ⟨1399845312000069350899987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7465841664000369871466597 1399845312000069350899987)
                    ·
                      rfl

theorem cell23_8178567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_8178567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178567 prefixEnd_8178567 := by exact prefixLift 8178567
  have htrace : WordTrace (prefixWord ++ tailWord_8178567) baseStart_8178567 baseEnd_8178567 := by
    simpa [prefixWord, tailWord_8178567, baseEnd_8178567] using wordTrace_append hprefix tailTrace_8178567
  have hstable : (prefixWord ++ tailWord_8178567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178567).length < 2 ^ (prefixWord ++ tailWord_8178567).sum := by decide
  have hdescent : baseEnd_8178567 < baseStart_8178567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178580 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 10]
def baseStart_8178580 : Nat := 118140960795 + 8178580 * 2 ^ 59
def prefixEnd_8178580 : Nat := 4983230072969 + 3 ^ 40 * 8178580 * 2
def baseEnd_8178580 : Nat := 466615845694301833537489

theorem tailTrace_8178580 : CollatzResearch.WordTrace tailWord_8178580 prefixEnd_8178580 466615845694301833537489 := by
  unfold tailWord_8178580
  simp only [CollatzResearch.WordTrace]
  refine ⟨149148659355204462552478597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198864879140272616736638129 149148659355204462552478597)
  ·
    refine ⟨27965373629100836728589737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149148659355204462552478597 27965373629100836728589737)
    ·
      refine ⟨20974030221825627546442303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27965373629100836728589737 20974030221825627546442303)
      ·
        refine ⟨31461045332738441319663455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20974030221825627546442303 31461045332738441319663455)
        ·
          refine ⟨47191567999107661979495183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31461045332738441319663455 47191567999107661979495183)
          ·
            refine ⟨70787351998661492969242775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47191567999107661979495183 70787351998661492969242775)
            ·
              refine ⟨106181027997992239453864163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70787351998661492969242775 106181027997992239453864163)
              ·
                refine ⟨159271541996988359180796245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106181027997992239453864163 159271541996988359180796245)
                ·
                  refine ⟨466615845694301833537489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 159271541996988359180796245 466615845694301833537489)
                  ·
                    rfl

theorem cell23_8178580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_8178580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178580 prefixEnd_8178580 := by exact prefixLift 8178580
  have htrace : WordTrace (prefixWord ++ tailWord_8178580) baseStart_8178580 baseEnd_8178580 := by
    simpa [prefixWord, tailWord_8178580, baseEnd_8178580] using wordTrace_append hprefix tailTrace_8178580
  have hstable : (prefixWord ++ tailWord_8178580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178580).length < 2 ^ (prefixWord ++ tailWord_8178580).sum := by decide
  have hdescent : baseEnd_8178580 < baseStart_8178580 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178594 : List Nat := [3, 3, 1, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_8178594 : Nat := 118140960795 + 8178594 * 2 ^ 59
def prefixEnd_8178594 : Nat := 4983230072969 + 3 ^ 40 * 8178594 * 2
def baseEnd_8178594 : Nat := 4199549799977879447062337

theorem tailTrace_8178594 : CollatzResearch.WordTrace tailWord_8178594 prefixEnd_8178594 4199549799977879447062337 := by
  unfold tailWord_8178594
  simp only [CollatzResearch.WordTrace]
  refine ⟨74574457333089551373991709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198865219554905470330644557 74574457333089551373991709)
  ·
    refine ⟨27965421499908581765246891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74574457333089551373991709 27965421499908581765246891)
    ·
      refine ⟨41948132249862872647870337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27965421499908581765246891 41948132249862872647870337)
      ·
        refine ⟨31461099187397154485902753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41948132249862872647870337 31461099187397154485902753)
        ·
          refine ⟨23595824390547865864427065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31461099187397154485902753 23595824390547865864427065)
          ·
            refine ⟨17696868292910899398320299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23595824390547865864427065 17696868292910899398320299)
            ·
              refine ⟨26545302439366349097480449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17696868292910899398320299 26545302439366349097480449)
              ·
                refine ⟨19908976829524761823110337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26545302439366349097480449 19908976829524761823110337)
                ·
                  refine ⟨14931732622143571367332753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19908976829524761823110337 14931732622143571367332753)
                  ·
                    refine ⟨11198799466607678525499565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14931732622143571367332753 11198799466607678525499565)
                    ·
                      refine ⟨4199549799977879447062337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11198799466607678525499565 4199549799977879447062337)
                      ·
                        rfl

theorem cell23_8178594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_8178594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178594 prefixEnd_8178594 := by exact prefixLift 8178594
  have htrace : WordTrace (prefixWord ++ tailWord_8178594) baseStart_8178594 baseEnd_8178594 := by
    simpa [prefixWord, tailWord_8178594, baseEnd_8178594] using wordTrace_append hprefix tailTrace_8178594
  have hstable : (prefixWord ++ tailWord_8178594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178594).length < 2 ^ (prefixWord ++ tailWord_8178594).sum := by decide
  have hdescent : baseEnd_8178594 < baseStart_8178594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178607 : List Nat := [1, 1, 2, 1, 2, 2, 2, 5, 3, 1, 3]
def baseStart_8178607 : Nat := 118140960795 + 8178607 * 2 ^ 59
def prefixEnd_8178607 : Nat := 4983230072969 + 3 ^ 40 * 8178607 * 2
def baseEnd_8178607 : Nat := 4199556475226387896199777

theorem tailTrace_8178607 : CollatzResearch.WordTrace tailWord_8178607 prefixEnd_8178607 4199556475226387896199777 := by
  unfold tailWord_8178607
  simp only [CollatzResearch.WordTrace]
  refine ⟨298298303481311108716190075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198865535654207405810793383 298298303481311108716190075)
  ·
    refine ⟨447447455221966663074285113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298298303481311108716190075 447447455221966663074285113)
    ·
      refine ⟨335585591416474997305713835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447447455221966663074285113 335585591416474997305713835)
      ·
        refine ⟨503378387124712495958570753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335585591416474997305713835 503378387124712495958570753)
        ·
          refine ⟨377533790343534371968928065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503378387124712495958570753 377533790343534371968928065)
          ·
            refine ⟨283150342757650778976696049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377533790343534371968928065 283150342757650778976696049)
            ·
              refine ⟨212362757068238084232522037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283150342757650778976696049 212362757068238084232522037)
              ·
                refine ⟨19909008475147320396798941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 212362757068238084232522037 19909008475147320396798941)
                ·
                  refine ⟨7465878178180245148799603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19909008475147320396798941 7465878178180245148799603)
                  ·
                    refine ⟨11198817267270367723199405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7465878178180245148799603 11198817267270367723199405)
                    ·
                      refine ⟨4199556475226387896199777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11198817267270367723199405 4199556475226387896199777)
                      ·
                        rfl

theorem cell23_8178607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 1, 3].length) (baseStart_8178607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178607 prefixEnd_8178607 := by exact prefixLift 8178607
  have htrace : WordTrace (prefixWord ++ tailWord_8178607) baseStart_8178607 baseEnd_8178607 := by
    simpa [prefixWord, tailWord_8178607, baseEnd_8178607] using wordTrace_append hprefix tailTrace_8178607
  have hstable : (prefixWord ++ tailWord_8178607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178607).length < 2 ^ (prefixWord ++ tailWord_8178607).sum := by decide
  have hdescent : baseEnd_8178607 < baseStart_8178607 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178660 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_8178660 : Nat := 118140960795 + 8178660 * 2 ^ 59
def prefixEnd_8178660 : Nat := 4983230072969 + 3 ^ 40 * 8178660 * 2
def baseEnd_8178660 : Nat := 4199583689701076188837033

theorem tailTrace_8178660 : CollatzResearch.WordTrace tailWord_8178660 prefixEnd_8178660 4199583689701076188837033 := by
  unfold tailWord_8178660
  simp only [CollatzResearch.WordTrace]
  refine ⟨149150118275059549383934717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198866824366746065845246289 149150118275059549383934717)
  ·
    refine ⟨55931294353147331018975519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149150118275059549383934717 55931294353147331018975519)
    ·
      refine ⟨83896941529720996528463279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55931294353147331018975519 83896941529720996528463279)
      ·
        refine ⟨125845412294581494792694919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83896941529720996528463279 125845412294581494792694919)
        ·
          refine ⟨188768118441872242189042379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125845412294581494792694919 188768118441872242189042379)
          ·
            refine ⟨283152177662808363283563569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188768118441872242189042379 283152177662808363283563569)
            ·
              refine ⟨212364133247106272462672677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283152177662808363283563569 212364133247106272462672677)
              ·
                refine ⟨39818274983832426086751127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212364133247106272462672677 39818274983832426086751127)
                ·
                  refine ⟨59727412475748639130126691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39818274983832426086751127 59727412475748639130126691)
                  ·
                    refine ⟨89591118713622958695190037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59727412475748639130126691 89591118713622958695190037)
                    ·
                      refine ⟨4199583689701076188837033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89591118713622958695190037 4199583689701076188837033)
                      ·
                        rfl

theorem cell23_8178660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_8178660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178660 prefixEnd_8178660 := by exact prefixLift 8178660
  have htrace : WordTrace (prefixWord ++ tailWord_8178660) baseStart_8178660 baseEnd_8178660 := by
    simpa [prefixWord, tailWord_8178660, baseEnd_8178660] using wordTrace_append hprefix tailTrace_8178660
  have hstable : (prefixWord ++ tailWord_8178660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178660).length < 2 ^ (prefixWord ++ tailWord_8178660).sum := by decide
  have hdescent : baseEnd_8178660 < baseStart_8178660 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178698 : List Nat := [3, 1, 2, 2, 3, 1, 1, 5, 1, 2, 2]
def baseStart_8178698 : Nat := 118140960795 + 8178698 * 2 ^ 59
def prefixEnd_8178698 : Nat := 4983230072969 + 3 ^ 40 * 8178698 * 2
def baseEnd_8178698 : Nat := 4199603201965947040161859

theorem tailTrace_8178698 : CollatzResearch.WordTrace tailWord_8178698 prefixEnd_8178698 4199603201965947040161859 := by
  unfold tailWord_8178698
  simp only [CollatzResearch.WordTrace]
  refine ⟨74575405630995357814438187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198867748349320954171835165 74575405630995357814438187)
  ·
    refine ⟨111863108446493036721657281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74575405630995357814438187 111863108446493036721657281)
    ·
      refine ⟨83897331334869777541242961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111863108446493036721657281 83897331334869777541242961)
      ·
        refine ⟨62922998501152333155932221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83897331334869777541242961 62922998501152333155932221)
        ·
          refine ⟨23596124437932124933474583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62922998501152333155932221 23596124437932124933474583)
          ·
            refine ⟨35394186656898187400211875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23596124437932124933474583 35394186656898187400211875)
            ·
              refine ⟨53091279985347281100317813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35394186656898187400211875 53091279985347281100317813)
              ·
                refine ⟨4977307498626307603154795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53091279985347281100317813 4977307498626307603154795)
                ·
                  refine ⟨7465961247939461404732193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4977307498626307603154795 7465961247939461404732193)
                  ·
                    refine ⟨5599470935954596053549145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7465961247939461404732193 5599470935954596053549145)
                    ·
                      refine ⟨4199603201965947040161859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5599470935954596053549145 4199603201965947040161859)
                      ·
                        rfl

theorem cell23_8178698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_8178698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178698 prefixEnd_8178698 := by exact prefixLift 8178698
  have htrace : WordTrace (prefixWord ++ tailWord_8178698) baseStart_8178698 baseEnd_8178698 := by
    simpa [prefixWord, tailWord_8178698, baseEnd_8178698] using wordTrace_append hprefix tailTrace_8178698
  have hstable : (prefixWord ++ tailWord_8178698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178698).length < 2 ^ (prefixWord ++ tailWord_8178698).sum := by decide
  have hdescent : baseEnd_8178698 < baseStart_8178698 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178714 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3]
def baseStart_8178714 : Nat := 118140960795 + 8178714 * 2 ^ 59
def prefixEnd_8178714 : Nat := 4983230072969 + 3 ^ 40 * 8178714 * 2
def baseEnd_8178714 : Nat := 4199611417656418977561785

theorem tailTrace_8178714 : CollatzResearch.WordTrace tailWord_8178714 prefixEnd_8178714 4199611417656418977561785 := by
  unfold tailWord_8178714
  simp only [CollatzResearch.WordTrace]
  refine ⟨74575551522980866497583799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198868137394615643993556797 74575551522980866497583799)
  ·
    refine ⟨111863327284471299746375699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74575551522980866497583799 111863327284471299746375699)
    ·
      refine ⟨167794990926706949619563549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111863327284471299746375699 167794990926706949619563549)
      ·
        refine ⟨62923121597515106107336331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167794990926706949619563549 62923121597515106107336331)
        ·
          refine ⟨94384682396272659161004497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62923121597515106107336331 94384682396272659161004497)
          ·
            refine ⟨70788511797204494370753373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94384682396272659161004497 70788511797204494370753373)
            ·
              refine ⟨26545691923951685389032515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70788511797204494370753373 26545691923951685389032515)
              ·
                refine ⟨39818537885927528083548773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26545691923951685389032515 39818537885927528083548773)
                ·
                  refine ⟨7465975853611411515665395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39818537885927528083548773 7465975853611411515665395)
                  ·
                    refine ⟨11198963780417117273498093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7465975853611411515665395 11198963780417117273498093)
                    ·
                      refine ⟨4199611417656418977561785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11198963780417117273498093 4199611417656418977561785)
                      ·
                        rfl

theorem cell23_8178714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_8178714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178714 prefixEnd_8178714 := by exact prefixLift 8178714
  have htrace : WordTrace (prefixWord ++ tailWord_8178714) baseStart_8178714 baseEnd_8178714 := by
    simpa [prefixWord, tailWord_8178714, baseEnd_8178714] using wordTrace_append hprefix tailTrace_8178714
  have hstable : (prefixWord ++ tailWord_8178714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178714).length < 2 ^ (prefixWord ++ tailWord_8178714).sum := by decide
  have hdescent : baseEnd_8178714 < baseStart_8178714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178731 : List Nat := [1, 1, 1, 1, 2, 1, 9, 1, 2, 1, 3]
def baseStart_8178731 : Nat := 118140960795 + 8178731 * 2 ^ 59
def prefixEnd_8178731 : Nat := 4983230072969 + 3 ^ 40 * 8178731 * 2
def baseEnd_8178731 : Nat := 4199620146827545411049207

theorem tailTrace_8178731 : CollatzResearch.WordTrace tailWord_8178731 prefixEnd_8178731 4199620146827545411049207 := by
  unfold tailWord_8178731
  simp only [CollatzResearch.WordTrace]
  refine ⟨298302826132861877893704047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198868550755241251929136031 298302826132861877893704047)
  ·
    refine ⟨447454239199292816840556071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298302826132861877893704047 447454239199292816840556071)
    ·
      refine ⟨671181358798939225260834107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447454239199292816840556071 671181358798939225260834107)
      ·
        refine ⟨1006772038198408837891251161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671181358798939225260834107 1006772038198408837891251161)
        ·
          refine ⟨755079028648806628418438371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1006772038198408837891251161 755079028648806628418438371)
          ·
            refine ⟨1132618542973209942627657557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755079028648806628418438371 1132618542973209942627657557)
            ·
              refine ⟨6636436775233652007583931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1132618542973209942627657557 6636436775233652007583931)
              ·
                refine ⟨9954655162850478011375897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6636436775233652007583931 9954655162850478011375897)
                ·
                  refine ⟨7465991372137858508531923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9954655162850478011375897 7465991372137858508531923)
                  ·
                    refine ⟨11198987058206787762797885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7465991372137858508531923 11198987058206787762797885)
                    ·
                      refine ⟨4199620146827545411049207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11198987058206787762797885 4199620146827545411049207)
                      ·
                        rfl

theorem cell23_8178731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 2, 1, 3].length) (baseStart_8178731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178731 prefixEnd_8178731 := by exact prefixLift 8178731
  have htrace : WordTrace (prefixWord ++ tailWord_8178731) baseStart_8178731 baseEnd_8178731 := by
    simpa [prefixWord, tailWord_8178731, baseEnd_8178731] using wordTrace_append hprefix tailTrace_8178731
  have hstable : (prefixWord ++ tailWord_8178731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178731).length < 2 ^ (prefixWord ++ tailWord_8178731).sum := by decide
  have hdescent : baseEnd_8178731 < baseStart_8178731 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178782 : List Nat := [4, 4, 1, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_8178782 : Nat := 118140960795 + 8178782 * 2 ^ 59
def prefixEnd_8178782 : Nat := 4983230072969 + 3 ^ 40 * 8178782 * 2
def baseEnd_8178782 : Nat := 4199646334340924711511473

theorem tailTrace_8178782 : CollatzResearch.WordTrace tailWord_8178782 prefixEnd_8178782 4199646334340924711511473 := by
  unfold tailWord_8178782
  simp only [CollatzResearch.WordTrace]
  refine ⟨37288085781959639200476325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198869790837118075735873733 37288085781959639200476325)
  ·
    refine ⟨6991516084117432350089311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37288085781959639200476325 6991516084117432350089311)
    ·
      refine ⟨10487274126176148525133967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6991516084117432350089311 10487274126176148525133967)
      ·
        refine ⟨15730911189264222787700951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10487274126176148525133967 15730911189264222787700951)
        ·
          refine ⟨23596366783896334181551427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15730911189264222787700951 23596366783896334181551427)
          ·
            refine ⟨35394550175844501272327141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23596366783896334181551427 35394550175844501272327141)
            ·
              refine ⟨6636478157970843988561339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35394550175844501272327141 6636478157970843988561339)
              ·
                refine ⟨9954717236956265982842009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6636478157970843988561339 9954717236956265982842009)
                ·
                  refine ⟨7466037927717199487131507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9954717236956265982842009 7466037927717199487131507)
                  ·
                    refine ⟨11199056891575799230697261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7466037927717199487131507 11199056891575799230697261)
                    ·
                      refine ⟨4199646334340924711511473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11199056891575799230697261 4199646334340924711511473)
                      ·
                        rfl

theorem cell23_8178782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_8178782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178782 prefixEnd_8178782 := by exact prefixLift 8178782
  have htrace : WordTrace (prefixWord ++ tailWord_8178782) baseStart_8178782 baseEnd_8178782 := by
    simpa [prefixWord, tailWord_8178782, baseEnd_8178782] using wordTrace_append hprefix tailTrace_8178782
  have hstable : (prefixWord ++ tailWord_8178782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178782).length < 2 ^ (prefixWord ++ tailWord_8178782).sum := by decide
  have hdescent : baseEnd_8178782 < baseStart_8178782 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178787 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 3]
def baseStart_8178787 : Nat := 118140960795 + 8178787 * 2 ^ 59
def prefixEnd_8178787 : Nat := 4983230072969 + 3 ^ 40 * 8178787 * 2
def baseEnd_8178787 : Nat := 4199648901744197191948949

theorem tailTrace_8178787 : CollatzResearch.WordTrace tailWord_8178787 prefixEnd_8178787 4199648901744197191948949 := by
  unfold tailWord_8178787
  simp only [CollatzResearch.WordTrace]
  refine ⟨298304868620658999457742615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198869912413772666305161743 298304868620658999457742615)
  ·
    refine ⟨447457302930988499186613923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298304868620658999457742615 447457302930988499186613923)
    ·
      refine ⟨671185954396482748779920885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447457302930988499186613923 671185954396482748779920885)
      ·
        refine ⟨62923683224670257698117583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 671185954396482748779920885 62923683224670257698117583)
        ·
          refine ⟨94385524837005386547176375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62923683224670257698117583 94385524837005386547176375)
          ·
            refine ⟨141578287255508079820764563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94385524837005386547176375 141578287255508079820764563)
            ·
              refine ⟨212367430883262119731146845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141578287255508079820764563 212367430883262119731146845)
              ·
                refine ⟨79637786581223294899180067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212367430883262119731146845 79637786581223294899180067)
                ·
                  refine ⟨119456679871834942348770101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79637786581223294899180067 119456679871834942348770101)
                  ·
                    refine ⟨11199063737984525845197197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119456679871834942348770101 11199063737984525845197197)
                    ·
                      refine ⟨4199648901744197191948949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11199063737984525845197197 4199648901744197191948949)
                      ·
                        rfl

theorem cell23_8178787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_8178787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178787 prefixEnd_8178787 := by exact prefixLift 8178787
  have htrace : WordTrace (prefixWord ++ tailWord_8178787) baseStart_8178787 baseEnd_8178787 := by
    simpa [prefixWord, tailWord_8178787, baseEnd_8178787] using wordTrace_append hprefix tailTrace_8178787
  have hstable : (prefixWord ++ tailWord_8178787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178787).length < 2 ^ (prefixWord ++ tailWord_8178787).sum := by decide
  have hdescent : baseEnd_8178787 < baseStart_8178787 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178792 : List Nat := [2, 1, 4, 4, 2, 1, 1, 2, 1, 3, 2]
def baseStart_8178792 : Nat := 118140960795 + 8178792 * 2 ^ 59
def prefixEnd_8178792 : Nat := 4983230072969 + 3 ^ 40 * 8178792 * 2
def baseEnd_8178792 : Nat := 4199651469147469672386427

theorem tailTrace_8178792 : CollatzResearch.WordTrace tailWord_8178792 prefixEnd_8178792 4199651469147469672386427 := by
  unfold tailWord_8178792
  simp only [CollatzResearch.WordTrace]
  refine ⟨149152525492820442655837315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198870033990427256874449753 149152525492820442655837315)
  ·
    refine ⟨223728788239230663983755973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149152525492820442655837315 223728788239230663983755973)
    ·
      refine ⟨41949147794855749496954245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223728788239230663983755973 41949147794855749496954245)
      ·
        refine ⟨7865465211535453030678921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41949147794855749496954245 7865465211535453030678921)
        ·
          refine ⟨5899098908651589773009191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7865465211535453030678921 5899098908651589773009191)
          ·
            refine ⟨8848648362977384659513787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5899098908651589773009191 8848648362977384659513787)
            ·
              refine ⟨13272972544466076989270681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8848648362977384659513787 13272972544466076989270681)
              ·
                refine ⟨9954729408349557741953011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13272972544466076989270681 9954729408349557741953011)
                ·
                  refine ⟨14932094112524336612929517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9954729408349557741953011 14932094112524336612929517)
                  ·
                    refine ⟨5599535292196626229848569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14932094112524336612929517 5599535292196626229848569)
                    ·
                      refine ⟨4199651469147469672386427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5599535292196626229848569 4199651469147469672386427)
                      ·
                        rfl

theorem cell23_8178792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_8178792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178792 prefixEnd_8178792 := by exact prefixLift 8178792
  have htrace : WordTrace (prefixWord ++ tailWord_8178792) baseStart_8178792 baseEnd_8178792 := by
    simpa [prefixWord, tailWord_8178792, baseEnd_8178792] using wordTrace_append hprefix tailTrace_8178792
  have hstable : (prefixWord ++ tailWord_8178792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178792).length < 2 ^ (prefixWord ++ tailWord_8178792).sum := by decide
  have hdescent : baseEnd_8178792 < baseStart_8178792 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178834 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_8178834 : Nat := 118140960795 + 8178834 * 2 ^ 59
def prefixEnd_8178834 : Nat := 4983230072969 + 3 ^ 40 * 8178834 * 2
def baseEnd_8178834 : Nat := 4199673035334958508061233

theorem tailTrace_8178834 : CollatzResearch.WordTrace tailWord_8178834 prefixEnd_8178834 4199673035334958508061233 := by
  unfold tailWord_8178834
  simp only [CollatzResearch.WordTrace]
  refine ⟨74576645712872181621175889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198871055234325817656469037 74576645712872181621175889)
  ·
    refine ⟨55932484284654136215881917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74576645712872181621175889 55932484284654136215881917)
    ·
      refine ⟨20974681606745301080955719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55932484284654136215881917 20974681606745301080955719)
      ·
        refine ⟨31462022410117951621433579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20974681606745301080955719 31462022410117951621433579)
        ·
          refine ⟨47193033615176927432150369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31462022410117951621433579 47193033615176927432150369)
          ·
            refine ⟨35394775211382695574112777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47193033615176927432150369 35394775211382695574112777)
            ·
              refine ⟨26546081408537021680584583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35394775211382695574112777 26546081408537021680584583)
              ·
                refine ⟨39819122112805532520876875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26546081408537021680584583 39819122112805532520876875)
                ·
                  refine ⟨59728683169208298781315313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39819122112805532520876875 59728683169208298781315313)
                  ·
                    refine ⟨44796512376906224085986485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59728683169208298781315313 44796512376906224085986485)
                    ·
                      refine ⟨4199673035334958508061233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44796512376906224085986485 4199673035334958508061233)
                      ·
                        rfl

theorem cell23_8178834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_8178834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178834 prefixEnd_8178834 := by exact prefixLift 8178834
  have htrace : WordTrace (prefixWord ++ tailWord_8178834) baseStart_8178834 baseEnd_8178834 := by
    simpa [prefixWord, tailWord_8178834, baseEnd_8178834] using wordTrace_append hprefix tailTrace_8178834
  have hstable : (prefixWord ++ tailWord_8178834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178834).length < 2 ^ (prefixWord ++ tailWord_8178834).sum := by decide
  have hdescent : baseEnd_8178834 < baseStart_8178834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178858 : List Nat := [3, 1, 5, 1, 1, 3, 1, 1, 2, 5]
def baseStart_8178858 : Nat := 118140960795 + 8178858 * 2 ^ 59
def prefixEnd_8178858 : Nat := 4983230072969 + 3 ^ 40 * 8178858 * 2
def baseEnd_8178858 : Nat := 1399895119623555471387041

theorem tailTrace_8178858 : CollatzResearch.WordTrace tailWord_8178858 prefixEnd_8178858 1399895119623555471387041 := by
  unfold tailWord_8178858
  simp only [CollatzResearch.WordTrace]
  refine ⟨74576864550850444645894307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198871638802267852389051485 74576864550850444645894307)
  ·
    refine ⟨111865296826275666968841461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74576864550850444645894307 111865296826275666968841461)
    ·
      refine ⟨10487371577463343778328887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111865296826275666968841461 10487371577463343778328887)
      ·
        refine ⟨15731057366195015667493331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10487371577463343778328887 15731057366195015667493331)
        ·
          refine ⟨23596586049292523501239997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15731057366195015667493331 23596586049292523501239997)
          ·
            refine ⟨8848719768484696312964999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23596586049292523501239997 8848719768484696312964999)
            ·
              refine ⟨13273079652727044469447499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8848719768484696312964999 13273079652727044469447499)
              ·
                refine ⟨19909619479090566704171249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13273079652727044469447499 19909619479090566704171249)
                ·
                  refine ⟨14932214609317925028128437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19909619479090566704171249 14932214609317925028128437)
                  ·
                    refine ⟨1399895119623555471387041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14932214609317925028128437 1399895119623555471387041)
                    ·
                      rfl

theorem cell23_8178858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_8178858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178858 prefixEnd_8178858 := by exact prefixLift 8178858
  have htrace : WordTrace (prefixWord ++ tailWord_8178858) baseStart_8178858 baseEnd_8178858 := by
    simpa [prefixWord, tailWord_8178858, baseEnd_8178858] using wordTrace_append hprefix tailTrace_8178858
  have hstable : (prefixWord ++ tailWord_8178858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178858).length < 2 ^ (prefixWord ++ tailWord_8178858).sum := by decide
  have hdescent : baseEnd_8178858 < baseStart_8178858 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178861 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_8178861 : Nat := 118140960795 + 8178861 * 2 ^ 59
def prefixEnd_8178861 : Nat := 4983230072969 + 3 ^ 40 * 8178861 * 2
def baseEnd_8178861 : Nat := 4199686899312629902423609

theorem tailTrace_8178861 : CollatzResearch.WordTrace tailWord_8178861 prefixEnd_8178861 4199686899312629902423609 := by
  unfold tailWord_8178861
  simp only [CollatzResearch.WordTrace]
  refine ⟨298307567622390910095936437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198871711748260606730624291 298307567622390910095936437)
  ·
    refine ⟨27966334464599147821494041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 298307567622390910095936437 27966334464599147821494041)
    ·
      refine ⟨20974750848449360866120531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27966334464599147821494041 20974750848449360866120531)
      ·
        refine ⟨31462126272674041299180797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20974750848449360866120531 31462126272674041299180797)
        ·
          refine ⟨11798297352252765487192799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31462126272674041299180797 11798297352252765487192799)
          ·
            refine ⟨17697446028379148230789199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11798297352252765487192799 17697446028379148230789199)
            ·
              refine ⟨26546169042568722346183799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17697446028379148230789199 26546169042568722346183799)
              ·
                refine ⟨39819253563853083519275699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26546169042568722346183799 39819253563853083519275699)
                ·
                  refine ⟨59728880345779625278913549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39819253563853083519275699 59728880345779625278913549)
                  ·
                    refine ⟨22398330129667359479592581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59728880345779625278913549 22398330129667359479592581)
                    ·
                      refine ⟨4199686899312629902423609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22398330129667359479592581 4199686899312629902423609)
                      ·
                        rfl

theorem cell23_8178861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_8178861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178861 prefixEnd_8178861 := by exact prefixLift 8178861
  have htrace : WordTrace (prefixWord ++ tailWord_8178861) baseStart_8178861 baseEnd_8178861 := by
    simpa [prefixWord, tailWord_8178861, baseEnd_8178861] using wordTrace_append hprefix tailTrace_8178861
  have hstable : (prefixWord ++ tailWord_8178861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178861).length < 2 ^ (prefixWord ++ tailWord_8178861).sum := by decide
  have hdescent : baseEnd_8178861 < baseStart_8178861 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178911 : List Nat := [1, 1, 2, 3, 2, 1, 4, 2, 3, 1, 3]
def baseStart_8178911 : Nat := 118140960795 + 8178911 * 2 ^ 59
def prefixEnd_8178911 : Nat := 4983230072969 + 3 ^ 40 * 8178911 * 2
def baseEnd_8178911 : Nat := 4199712573345354706798379

theorem tailTrace_8178911 : CollatzResearch.WordTrace tailWord_8178911 prefixEnd_8178911 4199712573345354706798379 := by
  unfold tailWord_8178911
  simp only [CollatzResearch.WordTrace]
  refine ⟨298309391272209768635256587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198872927514806512423504391 298309391272209768635256587)
  ·
    refine ⟨447464086908314652952884881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298309391272209768635256587 447464086908314652952884881)
    ·
      refine ⟨335598065181235989714663661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447464086908314652952884881 335598065181235989714663661)
      ·
        refine ⟨125849274442963496142998873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335598065181235989714663661 125849274442963496142998873)
        ·
          refine ⟨94386955832222622107249155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125849274442963496142998873 94386955832222622107249155)
          ·
            refine ⟨141580433748333933160873733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94386955832222622107249155 141580433748333933160873733)
            ·
              refine ⟨26546331327812612467663825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141580433748333933160873733 26546331327812612467663825)
              ·
                refine ⟨19909748495859459350747869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26546331327812612467663825 19909748495859459350747869)
                ·
                  refine ⟨7466155685947297256530451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19909748495859459350747869 7466155685947297256530451)
                  ·
                    refine ⟨11199233528920945884795677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7466155685947297256530451 11199233528920945884795677)
                    ·
                      refine ⟨4199712573345354706798379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11199233528920945884795677 4199712573345354706798379)
                      ·
                        rfl

theorem cell23_8178911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_8178911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178911 prefixEnd_8178911 := by exact prefixLift 8178911
  have htrace : WordTrace (prefixWord ++ tailWord_8178911) baseStart_8178911 baseEnd_8178911 := by
    simpa [prefixWord, tailWord_8178911, baseEnd_8178911] using wordTrace_append hprefix tailTrace_8178911
  have hstable : (prefixWord ++ tailWord_8178911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178911).length < 2 ^ (prefixWord ++ tailWord_8178911).sum := by decide
  have hdescent : baseEnd_8178911 < baseStart_8178911 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178932 : List Nat := [2, 6, 1, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_8178932 : Nat := 118140960795 + 8178932 * 2 ^ 59
def prefixEnd_8178932 : Nat := 4983230072969 + 3 ^ 40 * 8178932 * 2
def baseEnd_8178932 : Nat := 4199723356439099124635783

theorem tailTrace_8178932 : CollatzResearch.WordTrace tailWord_8178932 prefixEnd_8178932 4199723356439099124635783 := by
  unfold tailWord_8178932
  simp only [CollatzResearch.WordTrace]
  refine ⟨149155078602566844610885525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198873438136755792814514033 149155078602566844610885525)
  ·
    refine ⟨6991644309495320841135259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 149155078602566844610885525 6991644309495320841135259)
    ·
      refine ⟨10487466464242981261702889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6991644309495320841135259 10487466464242981261702889)
      ·
        refine ⟨7865599848182235946277167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10487466464242981261702889 7865599848182235946277167)
        ·
          refine ⟨11798399772273353919415751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7865599848182235946277167 11798399772273353919415751)
          ·
            refine ⟨17697599658410030879123627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11798399772273353919415751 17697599658410030879123627)
            ·
              refine ⟨26546399487615046318685441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17697599658410030879123627 26546399487615046318685441)
              ·
                refine ⟨19909799615711284739014081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26546399487615046318685441 19909799615711284739014081)
                ·
                  refine ⟨14932349711783463554260561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19909799615711284739014081 14932349711783463554260561)
                  ·
                    refine ⟨11199262283837597665695421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14932349711783463554260561 11199262283837597665695421)
                    ·
                      refine ⟨4199723356439099124635783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11199262283837597665695421 4199723356439099124635783)
                      ·
                        rfl

theorem cell23_8178932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_8178932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178932 prefixEnd_8178932 := by exact prefixLift 8178932
  have htrace : WordTrace (prefixWord ++ tailWord_8178932) baseStart_8178932 baseEnd_8178932 := by
    simpa [prefixWord, tailWord_8178932, baseEnd_8178932] using wordTrace_append hprefix tailTrace_8178932
  have hstable : (prefixWord ++ tailWord_8178932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178932).length < 2 ^ (prefixWord ++ tailWord_8178932).sum := by decide
  have hdescent : baseEnd_8178932 < baseStart_8178932 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178954 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3]
def baseStart_8178954 : Nat := 118140960795 + 8178954 * 2 ^ 59
def prefixEnd_8178954 : Nat := 4983230072969 + 3 ^ 40 * 8178954 * 2
def baseEnd_8178954 : Nat := 4199734653013498038560681

theorem tailTrace_8178954 : CollatzResearch.WordTrace tailWord_8178954 prefixEnd_8178954 4199734653013498038560681 := by
  unfold tailWord_8178954
  simp only [CollatzResearch.WordTrace]
  refine ⟨74577739902763496744767979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198873973074035991319381277 74577739902763496744767979)
  ·
    refine ⟨111866609854145245117151969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74577739902763496744767979 111866609854145245117151969)
    ·
      refine ⟨83899957390608933837863977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111866609854145245117151969 83899957390608933837863977)
      ·
        refine ⟨62924968042956700378397983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83899957390608933837863977 62924968042956700378397983)
        ·
          refine ⟨94387452064435050567596975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62924968042956700378397983 94387452064435050567596975)
          ·
            refine ⟨141581178096652575851395463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94387452064435050567596975 141581178096652575851395463)
            ·
              refine ⟨212371767144978863777093195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141581178096652575851395463 212371767144978863777093195)
              ·
                refine ⟨318557650717468295665639793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212371767144978863777093195 318557650717468295665639793)
                ·
                  refine ⟨238918238038101221749229845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318557650717468295665639793 238918238038101221749229845)
                  ·
                    refine ⟨11199292408035994769495149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 238918238038101221749229845 11199292408035994769495149)
                    ·
                      refine ⟨4199734653013498038560681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11199292408035994769495149 4199734653013498038560681)
                      ·
                        rfl

theorem cell23_8178954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_8178954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178954 prefixEnd_8178954 := by exact prefixLift 8178954
  have htrace : WordTrace (prefixWord ++ tailWord_8178954) baseStart_8178954 baseEnd_8178954 := by
    simpa [prefixWord, tailWord_8178954, baseEnd_8178954] using wordTrace_append hprefix tailTrace_8178954
  have hstable : (prefixWord ++ tailWord_8178954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178954).length < 2 ^ (prefixWord ++ tailWord_8178954).sum := by decide
  have hdescent : baseEnd_8178954 < baseStart_8178954 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178961 : List Nat := [1, 2, 2, 1, 1, 4, 3, 3, 2, 4]
def baseStart_8178961 : Nat := 118140960795 + 8178961 * 2 ^ 59
def prefixEnd_8178961 : Nat := 4983230072969 + 3 ^ 40 * 8178961 * 2
def baseEnd_8178961 : Nat := 1399912749126026503724383

theorem tailTrace_8178961 : CollatzResearch.WordTrace tailWord_8178961 prefixEnd_8178961 1399912749126026503724383 := by
  unfold tailWord_8178961
  simp only [CollatzResearch.WordTrace]
  refine ⟨298311214922028627174576737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198874143281352418116384491 298311214922028627174576737)
  ·
    refine ⟨223733411191521470380932553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298311214922028627174576737 223733411191521470380932553)
    ·
      refine ⟨167800058393641102785699415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223733411191521470380932553 167800058393641102785699415)
      ·
        refine ⟨251700087590461654178549123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167800058393641102785699415 251700087590461654178549123)
        ·
          refine ⟨377550131385692481267823685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251700087590461654178549123 377550131385692481267823685)
          ·
            refine ⟨70790649634817340237716941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 377550131385692481267823685 70790649634817340237716941)
            ·
              refine ⟨26546493613056502589143853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70790649634817340237716941 26546493613056502589143853)
              ·
                refine ⟨9954935104896188470928945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26546493613056502589143853 9954935104896188470928945)
                ·
                  refine ⟨7466201328672141353196709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9954935104896188470928945 7466201328672141353196709)
                  ·
                    refine ⟨1399912749126026503724383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7466201328672141353196709 1399912749126026503724383)
                    ·
                      rfl

theorem cell23_8178961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 4].length) (baseStart_8178961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178961 prefixEnd_8178961 := by exact prefixLift 8178961
  have htrace : WordTrace (prefixWord ++ tailWord_8178961) baseStart_8178961 baseEnd_8178961 := by
    simpa [prefixWord, tailWord_8178961, baseEnd_8178961] using wordTrace_append hprefix tailTrace_8178961
  have hstable : (prefixWord ++ tailWord_8178961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178961).length < 2 ^ (prefixWord ++ tailWord_8178961).sum := by decide
  have hdescent : baseEnd_8178961 < baseStart_8178961 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178968 : List Nat := [2, 1, 2, 3, 1, 5, 1, 2, 1, 1, 4]
def baseStart_8178968 : Nat := 118140960795 + 8178968 * 2 ^ 59
def prefixEnd_8178968 : Nat := 4983230072969 + 3 ^ 40 * 8178968 * 2
def baseEnd_8178968 : Nat := 4199741841742660983785617

theorem tailTrace_8178968 : CollatzResearch.WordTrace tailWord_8178968 prefixEnd_8178968 4199741841742660983785617 := by
  unfold tailWord_8178968
  simp only [CollatzResearch.WordTrace]
  refine ⟨149155735116501633685040779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198874313488668844913387705 149155735116501633685040779)
  ·
    refine ⟨223733602674752450527561169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149155735116501633685040779 223733602674752450527561169)
    ·
      refine ⟨167800202006064337895670877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223733602674752450527561169 167800202006064337895670877)
      ·
        refine ⟨62925075752274126710876579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167800202006064337895670877 62925075752274126710876579)
        ·
          refine ⟨94387613628411190066314869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62925075752274126710876579 94387613628411190066314869)
          ·
            refine ⟨8848838777663549068717019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94387613628411190066314869 8848838777663549068717019)
            ·
              refine ⟨13273258166495323603075529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8848838777663549068717019 13273258166495323603075529)
              ·
                refine ⟨9954943624871492702306647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13273258166495323603075529 9954943624871492702306647)
                ·
                  refine ⟨14932415437307239053459971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9954943624871492702306647 14932415437307239053459971)
                  ·
                    refine ⟨22398623155960858580189957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14932415437307239053459971 22398623155960858580189957)
                    ·
                      refine ⟨4199741841742660983785617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22398623155960858580189957 4199741841742660983785617)
                      ·
                        rfl

theorem cell23_8178968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_8178968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178968 prefixEnd_8178968 := by exact prefixLift 8178968
  have htrace : WordTrace (prefixWord ++ tailWord_8178968) baseStart_8178968 baseEnd_8178968 := by
    simpa [prefixWord, tailWord_8178968, baseEnd_8178968] using wordTrace_append hprefix tailTrace_8178968
  have hstable : (prefixWord ++ tailWord_8178968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178968).length < 2 ^ (prefixWord ++ tailWord_8178968).sum := by decide
  have hdescent : baseEnd_8178968 < baseStart_8178968 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8178981 : List Nat := [1, 3, 1, 2, 4, 2, 1, 2, 1, 2, 4]
def baseStart_8178981 : Nat := 118140960795 + 8178981 * 2 ^ 59
def prefixEnd_8178981 : Nat := 4983230072969 + 3 ^ 40 * 8178981 * 2
def baseEnd_8178981 : Nat := 4199748516991169432923057

theorem tailTrace_8178981 : CollatzResearch.WordTrace tailWord_8178981 prefixEnd_8178981 4199748516991169432923057 := by
  unfold tailWord_8178981
  simp only [CollatzResearch.WordTrace]
  refine ⟨298311944381956170590304797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198874629587970780393536531 298311944381956170590304797)
  ·
    refine ⟨111866979143233563971364299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298311944381956170590304797 111866979143233563971364299)
    ·
      refine ⟨167800468714850345957046449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111866979143233563971364299 167800468714850345957046449)
      ·
        refine ⟨125850351536137759467784837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167800468714850345957046449 125850351536137759467784837)
        ·
          refine ⟨23596940913025829900209657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125850351536137759467784837 23596940913025829900209657)
          ·
            refine ⟨17697705684769372425157243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23596940913025829900209657 17697705684769372425157243)
            ·
              refine ⟨26546558527154058637735865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17697705684769372425157243 26546558527154058637735865)
              ·
                refine ⟨19909918895365543978301899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26546558527154058637735865 19909918895365543978301899)
                ·
                  refine ⟨29864878343048315967452849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19909918895365543978301899 29864878343048315967452849)
                  ·
                    refine ⟨22398658757286236975589637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29864878343048315967452849 22398658757286236975589637)
                    ·
                      refine ⟨4199748516991169432923057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22398658757286236975589637 4199748516991169432923057)
                      ·
                        rfl

theorem cell23_8178981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_8178981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8178981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8178981 prefixEnd_8178981 := by exact prefixLift 8178981
  have htrace : WordTrace (prefixWord ++ tailWord_8178981) baseStart_8178981 baseEnd_8178981 := by
    simpa [prefixWord, tailWord_8178981, baseEnd_8178981] using wordTrace_append hprefix tailTrace_8178981
  have hstable : (prefixWord ++ tailWord_8178981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8178981).length < 2 ^ (prefixWord ++ tailWord_8178981).sum := by decide
  have hdescent : baseEnd_8178981 < baseStart_8178981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8178981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179004 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 2, 7]
def baseStart_8179004 : Nat := 118140960795 + 8179004 * 2 ^ 59
def prefixEnd_8179004 : Nat := 4983230072969 + 3 ^ 40 * 8179004 * 2
def baseEnd_8179004 : Nat := 1399920109015407614311817

theorem tailTrace_8179004 : CollatzResearch.WordTrace tailWord_8179004 prefixEnd_8179004 1399920109015407614311817 := by
  unfold tailWord_8179004
  simp only [CollatzResearch.WordTrace]
  refine ⟨149156391630436422759196033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198875188840581897012261377 149156391630436422759196033)
  ·
    refine ⟨111867293722827317069397025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149156391630436422759196033 111867293722827317069397025)
    ·
      refine ⟨83900470292120487802047769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111867293722827317069397025 83900470292120487802047769)
      ·
        refine ⟨62925352719090365851535827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83900470292120487802047769 62925352719090365851535827)
        ·
          refine ⟨94388029078635548777303741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62925352719090365851535827 94388029078635548777303741)
          ·
            refine ⟨35395510904488330791488903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94388029078635548777303741 35395510904488330791488903)
            ·
              refine ⟨53093266356732496187233355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35395510904488330791488903 53093266356732496187233355)
              ·
                refine ⟨79639899535098744280850033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53093266356732496187233355 79639899535098744280850033)
                ·
                  refine ⟨59729924651324058210637525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79639899535098744280850033 59729924651324058210637525)
                  ·
                    refine ⟨1399920109015407614311817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59729924651324058210637525 1399920109015407614311817)
                    ·
                      rfl

theorem cell23_8179004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_8179004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179004 prefixEnd_8179004 := by exact prefixLift 8179004
  have htrace : WordTrace (prefixWord ++ tailWord_8179004) baseStart_8179004 baseEnd_8179004 := by
    simpa [prefixWord, tailWord_8179004, baseEnd_8179004] using wordTrace_append hprefix tailTrace_8179004
  have hstable : (prefixWord ++ tailWord_8179004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179004).length < 2 ^ (prefixWord ++ tailWord_8179004).sum := by decide
  have hdescent : baseEnd_8179004 < baseStart_8179004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179024 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 4]
def baseStart_8179024 : Nat := 118140960795 + 8179024 * 2 ^ 59
def prefixEnd_8179024 : Nat := 4983230072969 + 3 ^ 40 * 8179024 * 2
def baseEnd_8179024 : Nat := 4199770596659312764685359

theorem tailTrace_8179024 : CollatzResearch.WordTrace tailWord_8179024 prefixEnd_8179024 4199770596659312764685359 := by
  unfold tailWord_8179024
  simp only [CollatzResearch.WordTrace]
  refine ⟨149156756360400194467060063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198875675147200259289413417 149156756360400194467060063)
  ·
    refine ⟨223735134540600291700590095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149156756360400194467060063 223735134540600291700590095)
    ·
      refine ⟨335602701810900437550885143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223735134540600291700590095 335602701810900437550885143)
      ·
        refine ⟨503404052716350656326327715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335602701810900437550885143 503404052716350656326327715)
        ·
          refine ⟨755106079074525984489491573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503404052716350656326327715 755106079074525984489491573)
          ·
            refine ⟨70791194913236811045889835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 755106079074525984489491573 70791194913236811045889835)
            ·
              refine ⟨106186792369855216568834753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70791194913236811045889835 106186792369855216568834753)
              ·
                refine ⟨79640094277391412426626065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106186792369855216568834753 79640094277391412426626065)
                ·
                  refine ⟨59730070708043559319969549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79640094277391412426626065 59730070708043559319969549)
                  ·
                    refine ⟨22398776515516334744988581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59730070708043559319969549 22398776515516334744988581)
                    ·
                      refine ⟨4199770596659312764685359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22398776515516334744988581 4199770596659312764685359)
                      ·
                        rfl

theorem cell23_8179024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 4].length) (baseStart_8179024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179024 prefixEnd_8179024 := by exact prefixLift 8179024
  have htrace : WordTrace (prefixWord ++ tailWord_8179024) baseStart_8179024 baseEnd_8179024 := by
    simpa [prefixWord, tailWord_8179024, baseEnd_8179024] using wordTrace_append hprefix tailTrace_8179024
  have hstable : (prefixWord ++ tailWord_8179024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179024).length < 2 ^ (prefixWord ++ tailWord_8179024).sum := by decide
  have hdescent : baseEnd_8179024 < baseStart_8179024 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179028 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 3, 3, 2]
def baseStart_8179028 : Nat := 118140960795 + 8179028 * 2 ^ 59
def prefixEnd_8179028 : Nat := 4983230072969 + 3 ^ 40 * 8179028 * 2
def baseEnd_8179028 : Nat := 4199772650581930749035341

theorem tailTrace_8179028 : CollatzResearch.WordTrace tailWord_8179028 prefixEnd_8179028 4199772650581930749035341 := by
  unfold tailWord_8179028
  simp only [CollatzResearch.WordTrace]
  refine ⟨149156829306392948808632869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198875772408523931744843825 149156829306392948808632869)
  ·
    refine ⟨27966905494948677901618663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149156829306392948808632869 27966905494948677901618663)
    ·
      refine ⟨41950358242423016852427995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27966905494948677901618663 41950358242423016852427995)
      ·
        refine ⟨62925537363634525278641993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41950358242423016852427995 62925537363634525278641993)
        ·
          refine ⟨47194153022725893958981495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62925537363634525278641993 47194153022725893958981495)
          ·
            refine ⟨70791229534088840938472243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47194153022725893958981495 70791229534088840938472243)
            ·
              refine ⟨106186844301133261407708365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70791229534088840938472243 106186844301133261407708365)
              ·
                refine ⟨39820066612924973027890637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106186844301133261407708365 39820066612924973027890637)
                ·
                  refine ⟨14932524979846864885458989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39820066612924973027890637 14932524979846864885458989)
                  ·
                    refine ⟨5599696867442574332047121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14932524979846864885458989 5599696867442574332047121)
                    ·
                      refine ⟨4199772650581930749035341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5599696867442574332047121 4199772650581930749035341)
                      ·
                        rfl

theorem cell23_8179028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_8179028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179028 prefixEnd_8179028 := by exact prefixLift 8179028
  have htrace : WordTrace (prefixWord ++ tailWord_8179028) baseStart_8179028 baseEnd_8179028 := by
    simpa [prefixWord, tailWord_8179028, baseEnd_8179028] using wordTrace_append hprefix tailTrace_8179028
  have hstable : (prefixWord ++ tailWord_8179028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179028).length < 2 ^ (prefixWord ++ tailWord_8179028).sum := by decide
  have hdescent : baseEnd_8179028 < baseStart_8179028 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179075 : List Nat := [1, 1, 1, 3, 5, 3, 1, 1, 1, 4, 2]
def baseStart_8179075 : Nat := 118140960795 + 8179075 * 2 ^ 59
def prefixEnd_8179075 : Nat := 4983230072969 + 3 ^ 40 * 8179075 * 2
def baseEnd_8179075 : Nat := 4199796784172692065147625

theorem tailTrace_8179075 : CollatzResearch.WordTrace tailWord_8179075 prefixEnd_8179075 4199796784172692065147625 := by
  unfold tailWord_8179075
  simp only [CollatzResearch.WordTrace]
  refine ⟨298315372843615624644226679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198876915229077083096151119 298315372843615624644226679)
  ·
    refine ⟨447473059265423436966340019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298315372843615624644226679 447473059265423436966340019)
    ·
      refine ⟨671209588898135155449510029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447473059265423436966340019 671209588898135155449510029)
      ·
        refine ⟨251703595836800683293566261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 671209588898135155449510029 251703595836800683293566261)
        ·
          refine ⟨23597212109700064058771837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 251703595836800683293566261 23597212109700064058771837)
          ·
            refine ⟨8848954541137524022039439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23597212109700064058771837 8848954541137524022039439)
            ·
              refine ⟨13273431811706286033059159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8848954541137524022039439 13273431811706286033059159)
              ·
                refine ⟨19910147717559429049588739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13273431811706286033059159 19910147717559429049588739)
                ·
                  refine ⟨29865221576339143574383109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19910147717559429049588739 29865221576339143574383109)
                  ·
                    refine ⟨5599729045563589420196833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29865221576339143574383109 5599729045563589420196833)
                    ·
                      refine ⟨4199796784172692065147625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5599729045563589420196833 4199796784172692065147625)
                      ·
                        rfl

theorem cell23_8179075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 4, 2].length) (baseStart_8179075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179075 prefixEnd_8179075 := by exact prefixLift 8179075
  have htrace : WordTrace (prefixWord ++ tailWord_8179075) baseStart_8179075 baseEnd_8179075 := by
    simpa [prefixWord, tailWord_8179075, baseEnd_8179075] using wordTrace_append hprefix tailTrace_8179075
  have hstable : (prefixWord ++ tailWord_8179075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179075).length < 2 ^ (prefixWord ++ tailWord_8179075).sum := by decide
  have hdescent : baseEnd_8179075 < baseStart_8179075 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179121 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 1, 2, 5]
def baseStart_8179121 : Nat := 118140960795 + 8179121 * 2 ^ 59
def prefixEnd_8179121 : Nat := 4983230072969 + 3 ^ 40 * 8179121 * 2
def baseEnd_8179121 : Nat := 4199820404282798885172413

theorem tailTrace_8179121 : CollatzResearch.WordTrace tailWord_8179121 prefixEnd_8179121 4199820404282798885172413 := by
  unfold tailWord_8179121
  simp only [CollatzResearch.WordTrace]
  refine ⟨298317050601448974500401217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198878033734299316333600811 298317050601448974500401217)
  ·
    refine ⟨223737787951086730875300913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298317050601448974500401217 223737787951086730875300913)
    ·
      refine ⟨167803340963315048156475685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223737787951086730875300913 167803340963315048156475685)
      ·
        refine ⟨31463126430621571529339191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167803340963315048156475685 31463126430621571529339191)
        ·
          refine ⟨47194689645932357294008787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31463126430621571529339191 47194689645932357294008787)
          ·
            refine ⟨70792034468898535941013181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47194689645932357294008787 70792034468898535941013181)
            ·
              refine ⟨26547012925836950977879943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70792034468898535941013181 26547012925836950977879943)
              ·
                refine ⟨39820519388755426466819915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26547012925836950977879943 39820519388755426466819915)
                ·
                  refine ⟨59730779083133139700229873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39820519388755426466819915 59730779083133139700229873)
                  ·
                    refine ⟨44798084312349854775172405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59730779083133139700229873 44798084312349854775172405)
                    ·
                      refine ⟨4199820404282798885172413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44798084312349854775172405 4199820404282798885172413)
                      ·
                        rfl

theorem cell23_8179121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_8179121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179121 prefixEnd_8179121 := by exact prefixLift 8179121
  have htrace : WordTrace (prefixWord ++ tailWord_8179121) baseStart_8179121 baseEnd_8179121 := by
    simpa [prefixWord, tailWord_8179121, baseEnd_8179121] using wordTrace_append hprefix tailTrace_8179121
  have hstable : (prefixWord ++ tailWord_8179121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179121).length < 2 ^ (prefixWord ++ tailWord_8179121).sum := by decide
  have hdescent : baseEnd_8179121 < baseStart_8179121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179148 : List Nat := [2, 2, 1, 4, 2, 1, 1, 3, 2, 1, 4]
def baseStart_8179148 : Nat := 118140960795 + 8179148 * 2 ^ 59
def prefixEnd_8179148 : Nat := 4983230072969 + 3 ^ 40 * 8179148 * 2
def baseEnd_8179148 : Nat := 4199834268260470279534789

theorem tailTrace_8179148 : CollatzResearch.WordTrace tailWord_8179148 prefixEnd_8179148 4199834268260470279534789 := by
  unfold tailWord_8179148
  simp only [CollatzResearch.WordTrace]
  refine ⟨149159017686175579055817049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198878690248234105407756065 149159017686175579055817049)
  ·
    refine ⟨111869263264631684291862787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149159017686175579055817049 111869263264631684291862787)
    ·
      refine ⟨167803894896947526437794181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111869263264631684291862787 167803894896947526437794181)
      ·
        refine ⟨31463230293177661207086409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167803894896947526437794181 31463230293177661207086409)
        ·
          refine ⟨23597422719883245905314807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31463230293177661207086409 23597422719883245905314807)
          ·
            refine ⟨35396134079824868857972211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23597422719883245905314807 35396134079824868857972211)
            ·
              refine ⟨53094201119737303286958317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35396134079824868857972211 53094201119737303286958317)
              ·
                refine ⟨19910325419901488732609369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53094201119737303286958317 19910325419901488732609369)
                ·
                  refine ⟨14932744064926116549457027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19910325419901488732609369 14932744064926116549457027)
                  ·
                    refine ⟨22399116097389174824185541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14932744064926116549457027 22399116097389174824185541)
                    ·
                      refine ⟨4199834268260470279534789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22399116097389174824185541 4199834268260470279534789)
                      ·
                        rfl

theorem cell23_8179148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_8179148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179148 prefixEnd_8179148 := by exact prefixLift 8179148
  have htrace : WordTrace (prefixWord ++ tailWord_8179148) baseStart_8179148 baseEnd_8179148 := by
    simpa [prefixWord, tailWord_8179148, baseEnd_8179148] using wordTrace_append hprefix tailTrace_8179148
  have hstable : (prefixWord ++ tailWord_8179148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179148).length < 2 ^ (prefixWord ++ tailWord_8179148).sum := by decide
  have hdescent : baseEnd_8179148 < baseStart_8179148 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179151 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 3]
def baseStart_8179151 : Nat := 118140960795 + 8179151 * 2 ^ 59
def prefixEnd_8179151 : Nat := 4983230072969 + 3 ^ 40 * 8179151 * 2
def baseEnd_8179151 : Nat := 4199835808702433767797275

theorem tailTrace_8179151 : CollatzResearch.WordTrace tailWord_8179151 prefixEnd_8179151 4199835808702433767797275 := by
  unfold tailWord_8179151
  simp only [CollatzResearch.WordTrace]
  refine ⟨298318144791340289623993307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198878763194226859749328871 298318144791340289623993307)
  ·
    refine ⟨447477217187010434435989961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298318144791340289623993307 447477217187010434435989961)
    ·
      refine ⟨335607912890257825826992471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447477217187010434435989961 335607912890257825826992471)
      ·
        refine ⟨503411869335386738740488707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335607912890257825826992471 503411869335386738740488707)
        ·
          refine ⟨755117804003080108110733061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503411869335386738740488707 755117804003080108110733061)
          ·
            refine ⟨141584588250577520270762449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 755117804003080108110733061 141584588250577520270762449)
            ·
              refine ⟨106188441187933140203071837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141584588250577520270762449 106188441187933140203071837)
              ·
                refine ⟨39820665445474927576151939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106188441187933140203071837 39820665445474927576151939)
                ·
                  refine ⟨59730998168212391364227909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39820665445474927576151939 59730998168212391364227909)
                  ·
                    refine ⟨11199562156539823380792733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59730998168212391364227909 11199562156539823380792733)
                    ·
                      refine ⟨4199835808702433767797275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11199562156539823380792733 4199835808702433767797275)
                      ·
                        rfl

theorem cell23_8179151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 3].length) (baseStart_8179151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179151 prefixEnd_8179151 := by exact prefixLift 8179151
  have htrace : WordTrace (prefixWord ++ tailWord_8179151) baseStart_8179151 baseEnd_8179151 := by
    simpa [prefixWord, tailWord_8179151, baseEnd_8179151] using wordTrace_append hprefix tailTrace_8179151
  have hstable : (prefixWord ++ tailWord_8179151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179151).length < 2 ^ (prefixWord ++ tailWord_8179151).sum := by decide
  have hdescent : baseEnd_8179151 < baseStart_8179151 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179202 : List Nat := [3, 4, 1, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_8179202 : Nat := 118140960795 + 8179202 * 2 ^ 59
def prefixEnd_8179202 : Nat := 4983230072969 + 3 ^ 40 * 8179202 * 2
def baseEnd_8179202 : Nat := 4199861996215813068259541

theorem tailTrace_8179202 : CollatzResearch.WordTrace tailWord_8179202 prefixEnd_8179202 4199861996215813068259541 := by
  unfold tailWord_8179202
  simp only [CollatzResearch.WordTrace]
  refine ⟨74580001228538881333524965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198880003276103683556066573 74580001228538881333524965)
  ·
    refine ⟨13983750230351040250035931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74580001228538881333524965 13983750230351040250035931)
    ·
      refine ⟨20975625345526560375053897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13983750230351040250035931 20975625345526560375053897)
      ·
        refine ⟨15731719009144920281290423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20975625345526560375053897 15731719009144920281290423)
        ·
          refine ⟨23597578513717380421935635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15731719009144920281290423 23597578513717380421935635)
          ·
            refine ⟨35396367770576070632903453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23597578513717380421935635 35396367770576070632903453)
            ·
              refine ⟨13273637913966026487338795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35396367770576070632903453 13273637913966026487338795)
              ·
                refine ⟨19910456870949039731008193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13273637913966026487338795 19910456870949039731008193)
                ·
                  refine ⟨14932842653211779798256145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19910456870949039731008193 14932842653211779798256145)
                  ·
                    refine ⟨11199631989908834848692109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14932842653211779798256145 11199631989908834848692109)
                    ·
                      refine ⟨4199861996215813068259541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11199631989908834848692109 4199861996215813068259541)
                      ·
                        rfl

theorem cell23_8179202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_8179202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179202 prefixEnd_8179202 := by exact prefixLift 8179202
  have htrace : WordTrace (prefixWord ++ tailWord_8179202) baseStart_8179202 baseEnd_8179202 := by
    simpa [prefixWord, tailWord_8179202, baseEnd_8179202] using wordTrace_append hprefix tailTrace_8179202
  have hstable : (prefixWord ++ tailWord_8179202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179202).length < 2 ^ (prefixWord ++ tailWord_8179202).sum := by decide
  have hdescent : baseEnd_8179202 < baseStart_8179202 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179231 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 3, 6]
def baseStart_8179231 : Nat := 118140960795 + 8179231 * 2 ^ 59
def prefixEnd_8179231 : Nat := 4983230072969 + 3 ^ 40 * 8179231 * 2
def baseEnd_8179231 : Nat := 1399958962384931151598969

theorem tailTrace_8179231 : CollatzResearch.WordTrace tailWord_8179231 prefixEnd_8179231 1399958962384931151598969 := by
  unfold tailWord_8179231
  simp only [CollatzResearch.WordTrace]
  refine ⟨298321062631050463286905547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198880708420700308857937031 298321062631050463286905547)
  ·
    refine ⟨447481593946575694930358321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298321062631050463286905547 447481593946575694930358321)
    ·
      refine ⟨335611195459931771197768741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447481593946575694930358321 335611195459931771197768741)
      ·
        refine ⟨62927099148737207099581639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335611195459931771197768741 62927099148737207099581639)
        ·
          refine ⟨94390648723105810649372459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62927099148737207099581639 94390648723105810649372459)
          ·
            refine ⟨141585973084658715974058689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94390648723105810649372459 141585973084658715974058689)
            ·
              refine ⟨106189479813494036980544017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141585973084658715974058689 106189479813494036980544017)
              ·
                refine ⟨79642109860120527735408013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106189479813494036980544017 79642109860120527735408013)
                ·
                  refine ⟨29865791197545197900778005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79642109860120527735408013 29865791197545197900778005)
                  ·
                    refine ⟨1399958962384931151598969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29865791197545197900778005 1399958962384931151598969)
                    ·
                      rfl

theorem cell23_8179231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 6].length) (baseStart_8179231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179231 prefixEnd_8179231 := by exact prefixLift 8179231
  have htrace : WordTrace (prefixWord ++ tailWord_8179231) baseStart_8179231 baseEnd_8179231 := by
    simpa [prefixWord, tailWord_8179231, baseEnd_8179231] using wordTrace_append hprefix tailTrace_8179231
  have hstable : (prefixWord ++ tailWord_8179231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179231).length < 2 ^ (prefixWord ++ tailWord_8179231).sum := by decide
  have hdescent : baseEnd_8179231 < baseStart_8179231 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179232 : List Nat := [2, 1, 1, 6, 1, 2, 2, 1, 3, 1, 3]
def baseStart_8179232 : Nat := 118140960795 + 8179232 * 2 ^ 59
def prefixEnd_8179232 : Nat := 4983230072969 + 3 ^ 40 * 8179232 * 2
def baseEnd_8179232 : Nat := 4199877400635447950884403

theorem tailTrace_8179232 : CollatzResearch.WordTrace tailWord_8179232 prefixEnd_8179232 4199877400635447950884403 := by
  unfold tailWord_8179232
  simp only [CollatzResearch.WordTrace]
  refine ⟨149160549552023420228845975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198880732736031226971794633 149160549552023420228845975)
  ·
    refine ⟨223740824328035130343268963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149160549552023420228845975 223740824328035130343268963)
    ·
      refine ⟨335611236492052695514903445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223740824328035130343268963 335611236492052695514903445)
      ·
        refine ⟨15731776710564970102261099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 335611236492052695514903445 15731776710564970102261099)
        ·
          refine ⟨23597665065847455153391649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15731776710564970102261099 23597665065847455153391649)
          ·
            refine ⟨17698248799385591365043737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23597665065847455153391649 17698248799385591365043737)
            ·
              refine ⟨13273686599539193523782803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17698248799385591365043737 13273686599539193523782803)
              ·
                refine ⟨19910529899308790285674205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13273686599539193523782803 19910529899308790285674205)
                ·
                  refine ⟨7466448712240796357127827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19910529899308790285674205 7466448712240796357127827)
                  ·
                    refine ⟨11199673068361194535691741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7466448712240796357127827 11199673068361194535691741)
                    ·
                      refine ⟨4199877400635447950884403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11199673068361194535691741 4199877400635447950884403)
                      ·
                        rfl

theorem cell23_8179232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_8179232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179232 prefixEnd_8179232 := by exact prefixLift 8179232
  have htrace : WordTrace (prefixWord ++ tailWord_8179232) baseStart_8179232 baseEnd_8179232 := by
    simpa [prefixWord, tailWord_8179232, baseEnd_8179232] using wordTrace_append hprefix tailTrace_8179232
  have hstable : (prefixWord ++ tailWord_8179232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179232).length < 2 ^ (prefixWord ++ tailWord_8179232).sum := by decide
  have hdescent : baseEnd_8179232 < baseStart_8179232 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179255 : List Nat := [1, 1, 3, 1, 2, 5, 2, 2, 1, 1, 4]
def baseStart_8179255 : Nat := 118140960795 + 8179255 * 2 ^ 59
def prefixEnd_8179255 : Nat := 4983230072969 + 3 ^ 40 * 8179255 * 2
def baseEnd_8179255 : Nat := 4199889210690501360896797

theorem tailTrace_8179255 : CollatzResearch.WordTrace tailWord_8179255 prefixEnd_8179255 4199889210690501360896797 := by
  unfold tailWord_8179255
  simp only [CollatzResearch.WordTrace]
  refine ⟨298321937982963515385779219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198881291988642343590519479 298321937982963515385779219)
  ·
    refine ⟨447482906974445273078668829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298321937982963515385779219 447482906974445273078668829)
    ·
      refine ⟨167806090115416977404500811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447482906974445273078668829 167806090115416977404500811)
      ·
        refine ⟨251709135173125466106751217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167806090115416977404500811 251709135173125466106751217)
        ·
          refine ⟨188781851379844099580063413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251709135173125466106751217 188781851379844099580063413)
          ·
            refine ⟨17698298566860384335630945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188781851379844099580063413 17698298566860384335630945)
            ·
              refine ⟨13273723925145288251723209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17698298566860384335630945 13273723925145288251723209)
              ·
                refine ⟨9955292943858966188792407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13273723925145288251723209 9955292943858966188792407)
                ·
                  refine ⟨14932939415788449283188611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9955292943858966188792407 14932939415788449283188611)
                  ·
                    refine ⟨22399409123682673924782917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14932939415788449283188611 22399409123682673924782917)
                    ·
                      refine ⟨4199889210690501360896797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22399409123682673924782917 4199889210690501360896797)
                      ·
                        rfl

theorem cell23_8179255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 1, 4].length) (baseStart_8179255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179255 prefixEnd_8179255 := by exact prefixLift 8179255
  have htrace : WordTrace (prefixWord ++ tailWord_8179255) baseStart_8179255 baseEnd_8179255 := by
    simpa [prefixWord, tailWord_8179255, baseEnd_8179255] using wordTrace_append hprefix tailTrace_8179255
  have hstable : (prefixWord ++ tailWord_8179255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179255).length < 2 ^ (prefixWord ++ tailWord_8179255).sum := by decide
  have hdescent : baseEnd_8179255 < baseStart_8179255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179309 : List Nat := [1, 5, 1, 1, 4, 2, 1, 2, 1, 2, 3]
def baseStart_8179309 : Nat := 118140960795 + 8179309 * 2 ^ 59
def prefixEnd_8179309 : Nat := 4983230072969 + 3 ^ 40 * 8179309 * 2
def baseEnd_8179309 : Nat := 4199916938645844149621549

theorem tailTrace_8179309 : CollatzResearch.WordTrace tailWord_8179309 prefixEnd_8179309 4199916938645844149621549 := by
  unfold tailWord_8179309
  simp only [CollatzResearch.WordTrace]
  refine ⟨298323907524767882608244981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198882605016511921738829987 298323907524767882608244981)
  ·
    refine ⟨27967866330446988994522967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 298323907524767882608244981 27967866330446988994522967)
    ·
      refine ⟨41951799495670483491784451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27967866330446988994522967 41951799495670483491784451)
      ·
        refine ⟨62927699243505725237676677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41951799495670483491784451 62927699243505725237676677)
        ·
          refine ⟨11798943608157323482064377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62927699243505725237676677 11798943608157323482064377)
          ·
            refine ⟨8849207706117992611548283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11798943608157323482064377 8849207706117992611548283)
            ·
              refine ⟨13273811559176988917322425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8849207706117992611548283 13273811559176988917322425)
              ·
                refine ⟨9955358669382741687991819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13273811559176988917322425 9955358669382741687991819)
                ·
                  refine ⟨14933038004074112531987729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9955358669382741687991819 14933038004074112531987729)
                  ·
                    refine ⟨11199778503055584398990797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14933038004074112531987729 11199778503055584398990797)
                    ·
                      refine ⟨4199916938645844149621549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11199778503055584398990797 4199916938645844149621549)
                      ·
                        rfl

theorem cell23_8179309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_8179309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179309 prefixEnd_8179309 := by exact prefixLift 8179309
  have htrace : WordTrace (prefixWord ++ tailWord_8179309) baseStart_8179309 baseEnd_8179309 := by
    simpa [prefixWord, tailWord_8179309, baseEnd_8179309] using wordTrace_append hprefix tailTrace_8179309
  have hstable : (prefixWord ++ tailWord_8179309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179309).length < 2 ^ (prefixWord ++ tailWord_8179309).sum := by decide
  have hdescent : baseEnd_8179309 < baseStart_8179309 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179311 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 8]
def baseStart_8179311 : Nat := 118140960795 + 8179311 * 2 ^ 59
def prefixEnd_8179311 : Nat := 4983230072969 + 3 ^ 40 * 8179311 * 2
def baseEnd_8179311 : Nat := 4199917965607153141796539

theorem tailTrace_8179311 : CollatzResearch.WordTrace tailWord_8179311 prefixEnd_8179311 4199917965607153141796539 := by
  unfold tailWord_8179311
  simp only [CollatzResearch.WordTrace]
  refine ⟨298323980470760636949817787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198882653647173757966545191 298323980470760636949817787)
  ·
    refine ⟨447485970706140955424726681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298323980470760636949817787 447485970706140955424726681)
    ·
      refine ⟨335614478029605716568545011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447485970706140955424726681 335614478029605716568545011)
      ·
        refine ⟨503421717044408574852817517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335614478029605716568545011 503421717044408574852817517)
        ·
          refine ⟨188783143891653215569806569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 503421717044408574852817517 188783143891653215569806569)
          ·
            refine ⟨141587357918739911677354927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188783143891653215569806569 141587357918739911677354927)
            ·
              refine ⟨212381036878109867516032391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141587357918739911677354927 212381036878109867516032391)
              ·
                refine ⟨318571555317164801274048587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212381036878109867516032391 318571555317164801274048587)
                ·
                  refine ⟨477857332975747201911072881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318571555317164801274048587 477857332975747201911072881)
                  ·
                    refine ⟨358392999731810401433304661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 477857332975747201911072881 358392999731810401433304661)
                    ·
                      refine ⟨4199917965607153141796539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 358392999731810401433304661 4199917965607153141796539)
                      ·
                        rfl

theorem cell23_8179311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_8179311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179311 prefixEnd_8179311 := by exact prefixLift 8179311
  have htrace : WordTrace (prefixWord ++ tailWord_8179311) baseStart_8179311 baseEnd_8179311 := by
    simpa [prefixWord, tailWord_8179311, baseEnd_8179311] using wordTrace_append hprefix tailTrace_8179311
  have hstable : (prefixWord ++ tailWord_8179311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179311).length < 2 ^ (prefixWord ++ tailWord_8179311).sum := by decide
  have hdescent : baseEnd_8179311 < baseStart_8179311 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179385 : List Nat := [1, 2, 1, 4, 1, 1, 3, 5, 5]
def baseStart_8179385 : Nat := 118140960795 + 8179385 * 2 ^ 59
def prefixEnd_8179385 : Nat := 4983230072969 + 3 ^ 40 * 8179385 * 2
def baseEnd_8179385 : Nat := 466661773686176205807911

theorem tailTrace_8179385 : CollatzResearch.WordTrace tailWord_8179385 prefixEnd_8179385 466661773686176205807911 := by
  unfold tailWord_8179385
  simp only [CollatzResearch.WordTrace]
  refine ⟨298326679472492547588011609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198884452981661698392007739 298326679472492547588011609)
  ·
    refine ⟨223745009604369410691008707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298326679472492547588011609 223745009604369410691008707)
    ·
      refine ⟨335617514406554116036513061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223745009604369410691008707 335617514406554116036513061)
      ·
        refine ⟨62928283951228896756846199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335617514406554116036513061 62928283951228896756846199)
        ·
          refine ⟨94392425926843345135269299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62928283951228896756846199 94392425926843345135269299)
          ·
            refine ⟨141588638890265017702903949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94392425926843345135269299 141588638890265017702903949)
            ·
              refine ⟨53095739583849381638588981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141588638890265017702903949 53095739583849381638588981)
              ·
                refine ⟨4977725585985879528617717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53095739583849381638588981 4977725585985879528617717)
                ·
                  refine ⟨466661773686176205807911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4977725585985879528617717 466661773686176205807911)
                  ·
                    rfl

theorem cell23_8179385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 5].length) (baseStart_8179385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179385 prefixEnd_8179385 := by exact prefixLift 8179385
  have htrace : WordTrace (prefixWord ++ tailWord_8179385) baseStart_8179385 baseEnd_8179385 := by
    simpa [prefixWord, tailWord_8179385, baseEnd_8179385] using wordTrace_append hprefix tailTrace_8179385
  have hstable : (prefixWord ++ tailWord_8179385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179385).length < 2 ^ (prefixWord ++ tailWord_8179385).sum := by decide
  have hdescent : baseEnd_8179385 < baseStart_8179385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179412 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_8179412 : Nat := 118140960795 + 8179412 * 2 ^ 59
def prefixEnd_8179412 : Nat := 4983230072969 + 3 ^ 40 * 8179412 * 2
def baseEnd_8179412 : Nat := 4199969827153257246633575

theorem tailTrace_8179412 : CollatzResearch.WordTrace tailWord_8179412 prefixEnd_8179412 4199969827153257246633575 := by
  unfold tailWord_8179412
  simp only [CollatzResearch.WordTrace]
  refine ⟨149163832121697365599622245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198885109495596487466162993 149163832121697365599622245)
  ·
    refine ⟨27968218522818256049929171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149163832121697365599622245 27968218522818256049929171)
    ·
      refine ⟨41952327784227384074893757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27968218522818256049929171 41952327784227384074893757)
      ·
        refine ⟨15732122919085269028085159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41952327784227384074893757 15732122919085269028085159)
        ·
          refine ⟨23598184378627903542127739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15732122919085269028085159 23598184378627903542127739)
          ·
            refine ⟨35397276567941855313191609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23598184378627903542127739 35397276567941855313191609)
            ·
              refine ⟨26547957425956391484893707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35397276567941855313191609 26547957425956391484893707)
              ·
                refine ⟨39821936138934587227340561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26547957425956391484893707 39821936138934587227340561)
                ·
                  refine ⟨29866452104200940420505421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39821936138934587227340561 29866452104200940420505421)
                  ·
                    refine ⟨11199919539075352657689533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29866452104200940420505421 11199919539075352657689533)
                    ·
                      refine ⟨4199969827153257246633575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11199919539075352657689533 4199969827153257246633575)
                      ·
                        rfl

theorem cell23_8179412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_8179412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179412 prefixEnd_8179412 := by exact prefixLift 8179412
  have htrace : WordTrace (prefixWord ++ tailWord_8179412) baseStart_8179412 baseEnd_8179412 := by
    simpa [prefixWord, tailWord_8179412, baseEnd_8179412] using wordTrace_append hprefix tailTrace_8179412
  have hstable : (prefixWord ++ tailWord_8179412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179412).length < 2 ^ (prefixWord ++ tailWord_8179412).sum := by decide
  have hdescent : baseEnd_8179412 < baseStart_8179412 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179428 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 2, 8]
def baseStart_8179428 : Nat := 118140960795 + 8179428 * 2 ^ 59
def prefixEnd_8179428 : Nat := 4983230072969 + 3 ^ 40 * 8179428 * 2
def baseEnd_8179428 : Nat := 1399992680947909728011167

theorem tailTrace_8179428 : CollatzResearch.WordTrace tailWord_8179428 prefixEnd_8179428 1399992680947909728011167 := by
  unfold tailWord_8179428
  simp only [CollatzResearch.WordTrace]
  refine ⟨149164123905668382965913469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198885498540891177287884625 149164123905668382965913469)
  ·
    refine ⟨55936546464625643612217551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149164123905668382965913469 55936546464625643612217551)
    ·
      refine ⟨83904819696938465418326327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55936546464625643612217551 83904819696938465418326327)
      ·
        refine ⟨125857229545407698127489491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83904819696938465418326327 125857229545407698127489491)
        ·
          refine ⟨188785844318111547191234237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125857229545407698127489491 188785844318111547191234237)
          ·
            refine ⟨70794691619291830196712839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188785844318111547191234237 70794691619291830196712839)
            ·
              refine ⟨106192037428937745295069259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70794691619291830196712839 106192037428937745295069259)
              ·
                refine ⟨159288056143406617942603889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106192037428937745295069259 159288056143406617942603889)
                ·
                  refine ⟨119466042107554963456952917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159288056143406617942603889 119466042107554963456952917)
                  ·
                    refine ⟨1399992680947909728011167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119466042107554963456952917 1399992680947909728011167)
                    ·
                      rfl

theorem cell23_8179428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_8179428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179428 prefixEnd_8179428 := by exact prefixLift 8179428
  have htrace : WordTrace (prefixWord ++ tailWord_8179428) baseStart_8179428 baseEnd_8179428 := by
    simpa [prefixWord, tailWord_8179428, baseEnd_8179428] using wordTrace_append hprefix tailTrace_8179428
  have hstable : (prefixWord ++ tailWord_8179428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179428).length < 2 ^ (prefixWord ++ tailWord_8179428).sum := by decide
  have hdescent : baseEnd_8179428 < baseStart_8179428 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179435 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 1, 6, 2]
def baseStart_8179435 : Nat := 118140960795 + 8179435 * 2 ^ 59
def prefixEnd_8179435 : Nat := 4983230072969 + 3 ^ 40 * 8179435 * 2
def baseEnd_8179435 : Nat := 4199981637208310656645969

theorem tailTrace_8179435 : CollatzResearch.WordTrace tailWord_8179435 prefixEnd_8179435 4199981637208310656645969 := by
  unfold tailWord_8179435
  simp only [CollatzResearch.WordTrace]
  refine ⟨298328503122311406127331759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198885668748207604084887839 298328503122311406127331759)
  ·
    refine ⟨447492754683467109190997639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298328503122311406127331759 447492754683467109190997639)
    ·
      refine ⟨671239132025200663786496459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447492754683467109190997639 671239132025200663786496459)
      ·
        refine ⟨1006858698037800995679744689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671239132025200663786496459 1006858698037800995679744689)
        ·
          refine ⟨755144023528350746759808517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1006858698037800995679744689 755144023528350746759808517)
          ·
            refine ⟨141589504411565765017464097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 755144023528350746759808517 141589504411565765017464097)
            ·
              refine ⟨106192128308674323763098073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141589504411565765017464097 106192128308674323763098073)
              ·
                refine ⟨79644096231505742822323555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106192128308674323763098073 79644096231505742822323555)
                ·
                  refine ⟨119466144347258614233485333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79644096231505742822323555 119466144347258614233485333)
                  ·
                    refine ⟨5599975516277747542194625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119466144347258614233485333 5599975516277747542194625)
                    ·
                      refine ⟨4199981637208310656645969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5599975516277747542194625 4199981637208310656645969)
                      ·
                        rfl

theorem cell23_8179435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 6, 2].length) (baseStart_8179435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179435 prefixEnd_8179435 := by exact prefixLift 8179435
  have htrace : WordTrace (prefixWord ++ tailWord_8179435) baseStart_8179435 baseEnd_8179435 := by
    simpa [prefixWord, tailWord_8179435, baseEnd_8179435] using wordTrace_append hprefix tailTrace_8179435
  have hstable : (prefixWord ++ tailWord_8179435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179435).length < 2 ^ (prefixWord ++ tailWord_8179435).sum := by decide
  have hdescent : baseEnd_8179435 < baseStart_8179435 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179448 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 2, 1, 6]
def baseStart_8179448 : Nat := 118140960795 + 8179448 * 2 ^ 59
def prefixEnd_8179448 : Nat := 4983230072969 + 3 ^ 40 * 8179448 * 2
def baseEnd_8179448 : Nat := 4199988312456819105783409

theorem tailTrace_8179448 : CollatzResearch.WordTrace tailWord_8179448 prefixEnd_8179448 4199988312456819105783409 := by
  unfold tailWord_8179448
  simp only [CollatzResearch.WordTrace]
  refine ⟨149164488635632154673777499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198885984847509539565036665 149164488635632154673777499)
  ·
    refine ⟨223746732953448232010666249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149164488635632154673777499 223746732953448232010666249)
    ·
      refine ⟨167810049715086174007999687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223746732953448232010666249 167810049715086174007999687)
      ·
        refine ⟨251715074572629261011999531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167810049715086174007999687 251715074572629261011999531)
        ·
          refine ⟨377572611858943891517999297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251715074572629261011999531 377572611858943891517999297)
          ·
            refine ⟨283179458894207918638499473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377572611858943891517999297 283179458894207918638499473)
            ·
              refine ⟨212384594170655938978874605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283179458894207918638499473 212384594170655938978874605)
              ·
                refine ⟨79644222813995977117077977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212384594170655938978874605 79644222813995977117077977)
                ·
                  refine ⟨59733167110496982837808483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79644222813995977117077977 59733167110496982837808483)
                  ·
                    refine ⟨89599750665745474256712725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59733167110496982837808483 89599750665745474256712725)
                    ·
                      refine ⟨4199988312456819105783409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89599750665745474256712725 4199988312456819105783409)
                      ·
                        rfl

theorem cell23_8179448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_8179448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179448 prefixEnd_8179448 := by exact prefixLift 8179448
  have htrace : WordTrace (prefixWord ++ tailWord_8179448) baseStart_8179448 baseEnd_8179448 := by
    simpa [prefixWord, tailWord_8179448, baseEnd_8179448] using wordTrace_append hprefix tailTrace_8179448
  have hstable : (prefixWord ++ tailWord_8179448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179448).length < 2 ^ (prefixWord ++ tailWord_8179448).sum := by decide
  have hdescent : baseEnd_8179448 < baseStart_8179448 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179455 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 3]
def baseStart_8179455 : Nat := 118140960795 + 8179455 * 2 ^ 59
def prefixEnd_8179455 : Nat := 4983230072969 + 3 ^ 40 * 8179455 * 2
def baseEnd_8179455 : Nat := 4199991906821400578395877

theorem tailTrace_8179455 : CollatzResearch.WordTrace tailWord_8179455 prefixEnd_8179455 4199991906821400578395877 := by
  unfold tailWord_8179455
  simp only [CollatzResearch.WordTrace]
  refine ⟨298329232582238949543059819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198886155054825966362039879 298329232582238949543059819)
  ·
    refine ⟨447493848873358424314589729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298329232582238949543059819 447493848873358424314589729)
    ·
      refine ⟨335620386655018818235942297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447493848873358424314589729 335620386655018818235942297)
      ·
        refine ⟨251715289991264113676956723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335620386655018818235942297 251715289991264113676956723)
        ·
          refine ⟨377572934986896170515435085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251715289991264113676956723 377572934986896170515435085)
          ·
            refine ⟨141589850620086063943288157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377572934986896170515435085 141589850620086063943288157)
            ·
              refine ⟨53096193982532273978733059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141589850620086063943288157 53096193982532273978733059)
              ·
                refine ⟨79644290973798410968099589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53096193982532273978733059 79644290973798410968099589)
                ·
                  refine ⟨14933304557587202056518673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79644290973798410968099589 14933304557587202056518673)
                  ·
                    refine ⟨11199978418190401542389005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14933304557587202056518673 11199978418190401542389005)
                    ·
                      refine ⟨4199991906821400578395877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11199978418190401542389005 4199991906821400578395877)
                      ·
                        rfl

theorem cell23_8179455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_8179455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179455 prefixEnd_8179455 := by exact prefixLift 8179455
  have htrace : WordTrace (prefixWord ++ tailWord_8179455) baseStart_8179455 baseEnd_8179455 := by
    simpa [prefixWord, tailWord_8179455, baseEnd_8179455] using wordTrace_append hprefix tailTrace_8179455
  have hstable : (prefixWord ++ tailWord_8179455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179455).length < 2 ^ (prefixWord ++ tailWord_8179455).sum := by decide
  have hdescent : baseEnd_8179455 < baseStart_8179455 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179525 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 5, 1, 4]
def baseStart_8179525 : Nat := 118140960795 + 8179525 * 2 ^ 59
def prefixEnd_8179525 : Nat := 4983230072969 + 3 ^ 40 * 8179525 * 2
def baseEnd_8179525 : Nat := 4200027850467215304520555

theorem tailTrace_8179525 : CollatzResearch.WordTrace tailWord_8179525 prefixEnd_8179525 4200027850467215304520555 := by
  unfold tailWord_8179525
  simp only [CollatzResearch.WordTrace]
  refine ⟨298331785691985351498108029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198887857127990234332072019 298331785691985351498108029)
  ·
    refine ⟨111874419634494506811790511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298331785691985351498108029 111874419634494506811790511)
    ·
      refine ⟨167811629451741760217685767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111874419634494506811790511 167811629451741760217685767)
      ·
        refine ⟨251717444177612640326528651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167811629451741760217685767 251717444177612640326528651)
        ·
          refine ⟨377576166266418960489792977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251717444177612640326528651 377576166266418960489792977)
          ·
            refine ⟨283182124699814220367344733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377576166266418960489792977 283182124699814220367344733)
            ·
              refine ⟨106193296762430332637754275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283182124699814220367344733 106193296762430332637754275)
              ·
                refine ⟨159289945143645498956631413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106193296762430332637754275 159289945143645498956631413)
                ·
                  refine ⟨14933432357216765527184195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159289945143645498956631413 14933432357216765527184195)
                  ·
                    refine ⟨22400148535825148290776293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14933432357216765527184195 22400148535825148290776293)
                    ·
                      refine ⟨4200027850467215304520555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22400148535825148290776293 4200027850467215304520555)
                      ·
                        rfl

theorem cell23_8179525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_8179525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179525 prefixEnd_8179525 := by exact prefixLift 8179525
  have htrace : WordTrace (prefixWord ++ tailWord_8179525) baseStart_8179525 baseEnd_8179525 := by
    simpa [prefixWord, tailWord_8179525, baseEnd_8179525] using wordTrace_append hprefix tailTrace_8179525
  have hstable : (prefixWord ++ tailWord_8179525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179525).length < 2 ^ (prefixWord ++ tailWord_8179525).sum := by decide
  have hdescent : baseEnd_8179525 < baseStart_8179525 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179556 : List Nat := [2, 3, 1, 1, 5, 2, 2, 1, 1, 5]
def baseStart_8179556 : Nat := 118140960795 + 8179556 * 2 ^ 59
def prefixEnd_8179556 : Nat := 4983230072969 + 3 ^ 40 * 8179556 * 2
def baseEnd_8179556 : Nat := 1400014589455834894410971

theorem tailTrace_8179556 : CollatzResearch.WordTrace tailWord_8179556 prefixEnd_8179556 1400014589455834894410971 := by
  unfold tailWord_8179556
  simp only [CollatzResearch.WordTrace]
  refine ⟨149166458177436521896243261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198888610903248695861657681 149166458177436521896243261)
  ·
    refine ⟨55937421816538695711091223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149166458177436521896243261 55937421816538695711091223)
    ·
      refine ⟨83906132724808043566636835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55937421816538695711091223 83906132724808043566636835)
      ·
        refine ⟨125859199087212065349955253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83906132724808043566636835 125859199087212065349955253)
        ·
          refine ⟨11799299914426131126558305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125859199087212065349955253 11799299914426131126558305)
          ·
            refine ⟨8849474935819598344918729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11799299914426131126558305 8849474935819598344918729)
            ·
              refine ⟨6637106201864698758689047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8849474935819598344918729 6637106201864698758689047)
              ·
                refine ⟨9955659302797048138033571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6637106201864698758689047 9955659302797048138033571)
                ·
                  refine ⟨14933488954195572207050357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9955659302797048138033571 14933488954195572207050357)
                  ·
                    refine ⟨1400014589455834894410971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14933488954195572207050357 1400014589455834894410971)
                    ·
                      rfl

theorem cell23_8179556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_8179556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179556 prefixEnd_8179556 := by exact prefixLift 8179556
  have htrace : WordTrace (prefixWord ++ tailWord_8179556) baseStart_8179556 baseEnd_8179556 := by
    simpa [prefixWord, tailWord_8179556, baseEnd_8179556] using wordTrace_append hprefix tailTrace_8179556
  have hstable : (prefixWord ++ tailWord_8179556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179556).length < 2 ^ (prefixWord ++ tailWord_8179556).sum := by decide
  have hdescent : baseEnd_8179556 < baseStart_8179556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179559 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 5, 2, 2]
def baseStart_8179559 : Nat := 118140960795 + 8179559 * 2 ^ 59
def prefixEnd_8179559 : Nat := 4983230072969 + 3 ^ 40 * 8179559 * 2
def baseEnd_8179559 : Nat := 4200045308809468171495399

theorem tailTrace_8179559 : CollatzResearch.WordTrace tailWord_8179559 prefixEnd_8179559 4200045308809468171495399 := by
  unfold tailWord_8179559
  simp only [CollatzResearch.WordTrace]
  refine ⟨298333025773862175304845731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198888683849241450203230487 298333025773862175304845731)
  ·
    refine ⟨447499538660793262957268597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298333025773862175304845731 447499538660793262957268597)
    ·
      refine ⟨41953081749449368402243931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 447499538660793262957268597 41953081749449368402243931)
      ·
        refine ⟨62929622624174052603365897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41953081749449368402243931 62929622624174052603365897)
        ·
          refine ⟨47197216968130539452524423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62929622624174052603365897 47197216968130539452524423)
          ·
            refine ⟨70795825452195809178786635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47197216968130539452524423 70795825452195809178786635)
            ·
              refine ⟨106193738178293713768179953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70795825452195809178786635 106193738178293713768179953)
              ·
                refine ⟨79645303633720285326134965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106193738178293713768179953 79645303633720285326134965)
                ·
                  refine ⟨7466747215661276749325153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79645303633720285326134965 7466747215661276749325153)
                  ·
                    refine ⟨5600060411745957561993865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7466747215661276749325153 5600060411745957561993865)
                    ·
                      refine ⟨4200045308809468171495399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5600060411745957561993865 4200045308809468171495399)
                      ·
                        rfl

theorem cell23_8179559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_8179559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179559 prefixEnd_8179559 := by exact prefixLift 8179559
  have htrace : WordTrace (prefixWord ++ tailWord_8179559) baseStart_8179559 baseEnd_8179559 := by
    simpa [prefixWord, tailWord_8179559, baseEnd_8179559] using wordTrace_append hprefix tailTrace_8179559
  have hstable : (prefixWord ++ tailWord_8179559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179559).length < 2 ^ (prefixWord ++ tailWord_8179559).sum := by decide
  have hdescent : baseEnd_8179559 < baseStart_8179559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179575 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 3]
def baseStart_8179575 : Nat := 118140960795 + 8179575 * 2 ^ 59
def prefixEnd_8179575 : Nat := 4983230072969 + 3 ^ 40 * 8179575 * 2
def baseEnd_8179575 : Nat := 4200053524499940108895325

theorem tailTrace_8179575 : CollatzResearch.WordTrace tailWord_8179575 prefixEnd_8179575 4200053524499940108895325 := by
  unfold tailWord_8179575
  simp only [CollatzResearch.WordTrace]
  refine ⟨298333609341804210037428179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198889072894536140024952119 298333609341804210037428179)
  ·
    refine ⟨447500414012706315056142269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298333609341804210037428179 447500414012706315056142269)
    ·
      refine ⟨167812655254764868146053351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447500414012706315056142269 167812655254764868146053351)
      ·
        refine ⟨251718982882147302219080027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167812655254764868146053351 251718982882147302219080027)
        ·
          refine ⟨377578474323220953328620041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251718982882147302219080027 377578474323220953328620041)
          ·
            refine ⟨283183855742415714996465031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377578474323220953328620041 283183855742415714996465031)
            ·
              refine ⟨424775783613623572494697547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283183855742415714996465031 424775783613623572494697547)
              ·
                refine ⟨637163675420435358742046321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424775783613623572494697547 637163675420435358742046321)
                ·
                  refine ⟨477872756565326519056534741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637163675420435358742046321 477872756565326519056534741)
                  ·
                    refine ⟨11200142731999840290387533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 477872756565326519056534741 11200142731999840290387533)
                    ·
                      refine ⟨4200053524499940108895325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11200142731999840290387533 4200053524499940108895325)
                      ·
                        rfl

theorem cell23_8179575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_8179575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179575 prefixEnd_8179575 := by exact prefixLift 8179575
  have htrace : WordTrace (prefixWord ++ tailWord_8179575) baseStart_8179575 baseEnd_8179575 := by
    simpa [prefixWord, tailWord_8179575, baseEnd_8179575] using wordTrace_append hprefix tailTrace_8179575
  have hstable : (prefixWord ++ tailWord_8179575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179575).length < 2 ^ (prefixWord ++ tailWord_8179575).sum := by decide
  have hdescent : baseEnd_8179575 < baseStart_8179575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179605 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_8179605 : Nat := 118140960795 + 8179605 * 2 ^ 59
def prefixEnd_8179605 : Nat := 4983230072969 + 3 ^ 40 * 8179605 * 2
def baseEnd_8179605 : Nat := 4200068928919574991520187

theorem tailTrace_8179605 : CollatzResearch.WordTrace tailWord_8179605 prefixEnd_8179605 4200068928919574991520187 := by
  unfold tailWord_8179605
  simp only [CollatzResearch.WordTrace]
  refine ⟨298334703531695525161020269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198889802354463683440680179 298334703531695525161020269)
  ·
    refine ⟨111875513824385821935382601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298334703531695525161020269 111875513824385821935382601)
    ·
      refine ⟨83906635368289366451536951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111875513824385821935382601 83906635368289366451536951)
      ·
        refine ⟨125859953052434049677305427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83906635368289366451536951 125859953052434049677305427)
        ·
          refine ⟨188789929578651074515958141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125859953052434049677305427 188789929578651074515958141)
          ·
            refine ⟨70796223591994152943484303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188789929578651074515958141 70796223591994152943484303)
            ·
              refine ⟨106194335387991229415226455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70796223591994152943484303 106194335387991229415226455)
              ·
                refine ⟨159291503081986844122839683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106194335387991229415226455 159291503081986844122839683)
                ·
                  refine ⟨238937254622980266184259525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159291503081986844122839683 238937254622980266184259525)
                  ·
                    refine ⟨44800735241808799909548661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 238937254622980266184259525 44800735241808799909548661)
                    ·
                      refine ⟨4200068928919574991520187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44800735241808799909548661 4200068928919574991520187)
                      ·
                        rfl

theorem cell23_8179605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_8179605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179605 prefixEnd_8179605 := by exact prefixLift 8179605
  have htrace : WordTrace (prefixWord ++ tailWord_8179605) baseStart_8179605 baseEnd_8179605 := by
    simpa [prefixWord, tailWord_8179605, baseEnd_8179605] using wordTrace_append hprefix tailTrace_8179605
  have hstable : (prefixWord ++ tailWord_8179605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179605).length < 2 ^ (prefixWord ++ tailWord_8179605).sum := by decide
  have hdescent : baseEnd_8179605 < baseStart_8179605 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179610 : List Nat := [3, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2]
def baseStart_8179610 : Nat := 118140960795 + 8179610 * 2 ^ 59
def prefixEnd_8179610 : Nat := 4983230072969 + 3 ^ 40 * 8179610 * 2
def baseEnd_8179610 : Nat := 4200071496322847471957665

theorem tailTrace_8179610 : CollatzResearch.WordTrace tailWord_8179610 prefixEnd_8179610 4200071496322847471957665 := by
  unfold tailWord_8179610
  simp only [CollatzResearch.WordTrace]
  refine ⟨74583721474169352753738071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198889923931118274009968189 74583721474169352753738071)
  ·
    refine ⟨111875582211254029130607107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74583721474169352753738071 111875582211254029130607107)
    ·
      refine ⟨167813373316881043695910661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111875582211254029130607107 167813373316881043695910661)
      ·
        refine ⟨31465007496915195692983249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167813373316881043695910661 31465007496915195692983249)
        ·
          refine ⟨23598755622686396769737437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31465007496915195692983249 23598755622686396769737437)
          ·
            refine ⟨8849533358507398788651539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23598755622686396769737437 8849533358507398788651539)
            ·
              refine ⟨13274300037761098182977309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8849533358507398788651539 13274300037761098182977309)
              ·
                refine ⟨4977862514160411818616491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13274300037761098182977309 4977862514160411818616491)
                ·
                  refine ⟨7466793771240617727924737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4977862514160411818616491 7466793771240617727924737)
                  ·
                    refine ⟨5600095328430463295943553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7466793771240617727924737 5600095328430463295943553)
                    ·
                      refine ⟨4200071496322847471957665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5600095328430463295943553 4200071496322847471957665)
                      ·
                        rfl

theorem cell23_8179610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_8179610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179610 prefixEnd_8179610 := by exact prefixLift 8179610
  have htrace : WordTrace (prefixWord ++ tailWord_8179610) baseStart_8179610 baseEnd_8179610 := by
    simpa [prefixWord, tailWord_8179610, baseEnd_8179610] using wordTrace_append hprefix tailTrace_8179610
  have hstable : (prefixWord ++ tailWord_8179610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179610).length < 2 ^ (prefixWord ++ tailWord_8179610).sum := by decide
  have hdescent : baseEnd_8179610 < baseStart_8179610 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179625 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 2, 6]
def baseStart_8179625 : Nat := 118140960795 + 8179625 * 2 ^ 59
def prefixEnd_8179625 : Nat := 4983230072969 + 3 ^ 40 * 8179625 * 2
def baseEnd_8179625 : Nat := 1400026399510888304423365

theorem tailTrace_8179625 : CollatzResearch.WordTrace tailWord_8179625 prefixEnd_8179625 1400026399510888304423365 := by
  unfold tailWord_8179625
  simp only [CollatzResearch.WordTrace]
  refine ⟨298335432991623068576748329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198890288661082045717832219 298335432991623068576748329)
  ·
    refine ⟨223751574743717301432561247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298335432991623068576748329 223751574743717301432561247)
    ·
      refine ⟨335627362115575952148841871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223751574743717301432561247 335627362115575952148841871)
      ·
        refine ⟨503441043173363928223262807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335627362115575952148841871 503441043173363928223262807)
        ·
          refine ⟨755161564760045892334894211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503441043173363928223262807 755161564760045892334894211)
          ·
            refine ⟨1132742347140068838502341317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755161564760045892334894211 1132742347140068838502341317)
            ·
              refine ⟨212389190088762907219188997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1132742347140068838502341317 212389190088762907219188997)
              ·
                refine ⟨39822973141643045103597937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212389190088762907219188997 39822973141643045103597937)
                ·
                  refine ⟨29867229856232283827698453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39822973141643045103597937 29867229856232283827698453)
                  ·
                    refine ⟨1400026399510888304423365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29867229856232283827698453 1400026399510888304423365)
                    ·
                      rfl

theorem cell23_8179625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 6].length) (baseStart_8179625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179625 prefixEnd_8179625 := by exact prefixLift 8179625
  have htrace : WordTrace (prefixWord ++ tailWord_8179625) baseStart_8179625 baseEnd_8179625 := by
    simpa [prefixWord, tailWord_8179625, baseEnd_8179625] using wordTrace_append hprefix tailTrace_8179625
  have hstable : (prefixWord ++ tailWord_8179625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179625).length < 2 ^ (prefixWord ++ tailWord_8179625).sum := by decide
  have hdescent : baseEnd_8179625 < baseStart_8179625 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8179635 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 5]
def baseStart_8179635 : Nat := 118140960795 + 8179635 * 2 ^ 59
def prefixEnd_8179635 : Nat := 4983230072969 + 3 ^ 40 * 8179635 * 2
def baseEnd_8179635 : Nat := 4200084333339209874145049

theorem tailTrace_8179635 : CollatzResearch.WordTrace tailWord_8179635 prefixEnd_8179635 4200084333339209874145049 := by
  unfold tailWord_8179635
  simp only [CollatzResearch.WordTrace]
  refine ⟨298335797721586840284612359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198890531814391226856408239 298335797721586840284612359)
  ·
    refine ⟨447503696582380260426918539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298335797721586840284612359 447503696582380260426918539)
    ·
      refine ⟨671255544873570390640377809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447503696582380260426918539 671255544873570390640377809)
      ·
        refine ⟨503441658655177792980283357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 671255544873570390640377809 503441658655177792980283357)
        ·
          refine ⟨188790621995691672367606259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 503441658655177792980283357 188790621995691672367606259)
          ·
            refine ⟨283185932993537508551409389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188790621995691672367606259 283185932993537508551409389)
            ·
              refine ⟨106194724872576565706778521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283185932993537508551409389 106194724872576565706778521)
              ·
                refine ⟨79646043654432424280083891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106194724872576565706778521 79646043654432424280083891)
                ·
                  refine ⟨119469065481648636420125837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79646043654432424280083891 119469065481648636420125837)
                  ·
                    refine ⟨44800899555618238657547189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119469065481648636420125837 44800899555618238657547189)
                    ·
                      refine ⟨4200084333339209874145049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44800899555618238657547189 4200084333339209874145049)
                      ·
                        rfl

theorem cell23_8179635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_8179635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8179635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8179635 prefixEnd_8179635 := by exact prefixLift 8179635
  have htrace : WordTrace (prefixWord ++ tailWord_8179635) baseStart_8179635 baseEnd_8179635 := by
    simpa [prefixWord, tailWord_8179635, baseEnd_8179635] using wordTrace_append hprefix tailTrace_8179635
  have hstable : (prefixWord ++ tailWord_8179635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8179635).length < 2 ^ (prefixWord ++ tailWord_8179635).sum := by decide
  have hdescent : baseEnd_8179635 < baseStart_8179635 := by decide
  rcases family_descends (prefixWord ++ tailWord_8179635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
