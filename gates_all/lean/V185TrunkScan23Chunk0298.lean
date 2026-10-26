import V185TrunkScan23Chunk0297

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1762672 : List Nat := [2, 1, 1, 1, 4, 2, 2, 4, 2, 4]
def baseStart_1762672 : Nat := 118140960795 + 1762672 * 2 ^ 59
def prefixEnd_1762672 : Nat := 4983230072969 + 3 ^ 40 * 1762672 * 2
def baseEnd_1762672 : Nat := 301699324074010923797875

theorem tailTrace_1762672 : CollatzResearch.WordTrace tailWord_1762672 prefixEnd_1762672 301699324074010923797875 := by
  unfold tailWord_1762672
  simp only [CollatzResearch.WordTrace]
  refine ⟨32144964735073929627829135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42859952980098572837105513 32144964735073929627829135)
  ·
    refine ⟨48217447102610894441743703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32144964735073929627829135 48217447102610894441743703)
    ·
      refine ⟨72326170653916341662615555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48217447102610894441743703 72326170653916341662615555)
      ·
        refine ⟨108489255980874512493923333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72326170653916341662615555 108489255980874512493923333)
        ·
          refine ⟨20341735496413971092610625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108489255980874512493923333 20341735496413971092610625)
          ·
            refine ⟨15256301622310478319457969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20341735496413971092610625 15256301622310478319457969)
            ·
              refine ⟨11442226216732858739593477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15256301622310478319457969 11442226216732858739593477)
              ·
                refine ⟨2145417415637411013673777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11442226216732858739593477 2145417415637411013673777)
                ·
                  refine ⟨1609063061728058260255333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2145417415637411013673777 1609063061728058260255333)
                  ·
                    refine ⟨301699324074010923797875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1609063061728058260255333 301699324074010923797875)
                    ·
                      rfl

theorem cell23_1762672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 2, 4].length) (baseStart_1762672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762672 prefixEnd_1762672 := by exact prefixLift 1762672
  have htrace : WordTrace (prefixWord ++ tailWord_1762672) baseStart_1762672 baseEnd_1762672 := by
    simpa [prefixWord, tailWord_1762672, baseEnd_1762672] using wordTrace_append hprefix tailTrace_1762672
  have hstable : (prefixWord ++ tailWord_1762672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762672).length < 2 ^ (prefixWord ++ tailWord_1762672).sum := by decide
  have hdescent : baseEnd_1762672 < baseStart_1762672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762685 : List Nat := [1, 4, 1, 1, 2, 2, 4, 8]
def baseStart_1762685 : Nat := 118140960795 + 1762685 * 2 ^ 59
def prefixEnd_1762685 : Nat := 4983230072969 + 3 ^ 40 * 1762685 * 2
def baseEnd_1762685 : Nat := 33522394350760785945595

theorem tailTrace_1762685 : CollatzResearch.WordTrace tailWord_1762685 prefixEnd_1762685 33522394350760785945595 := by
  unfold tailWord_1762685
  simp only [CollatzResearch.WordTrace]
  refine ⟨64290403619100762475881509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42860269079400508317254339 64290403619100762475881509)
  ·
    refine ⟨12054450678581392964227783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64290403619100762475881509 12054450678581392964227783)
    ·
      refine ⟨18081676017872089446341675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12054450678581392964227783 18081676017872089446341675)
      ·
        refine ⟨27122514026808134169512513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18081676017872089446341675 27122514026808134169512513)
        ·
          refine ⟨20341885520106100627134385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27122514026808134169512513 20341885520106100627134385)
          ·
            refine ⟨15256414140079575470350789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20341885520106100627134385 15256414140079575470350789)
            ·
              refine ⟨2860577651264920400690773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15256414140079575470350789 2860577651264920400690773)
              ·
                refine ⟨33522394350760785945595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2860577651264920400690773 33522394350760785945595)
                ·
                  rfl

theorem cell23_1762685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 8].length) (baseStart_1762685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762685 prefixEnd_1762685 := by exact prefixLift 1762685
  have htrace : WordTrace (prefixWord ++ tailWord_1762685) baseStart_1762685 baseEnd_1762685 := by
    simpa [prefixWord, tailWord_1762685, baseEnd_1762685] using wordTrace_append hprefix tailTrace_1762685
  have hstable : (prefixWord ++ tailWord_1762685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762685).length < 2 ^ (prefixWord ++ tailWord_1762685).sum := by decide
  have hdescent : baseEnd_1762685 < baseStart_1762685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762716 : List Nat := [2, 2, 3, 4, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1762716 : Nat := 118140960795 + 1762716 * 2 ^ 59
def prefixEnd_1762716 : Nat := 4983230072969 + 3 ^ 40 * 1762716 * 2
def baseEnd_1762716 : Nat := 905120565370830599243423

theorem tailTrace_1762716 : CollatzResearch.WordTrace tailWord_1762716 prefixEnd_1762716 905120565370830599243423 := by
  unfold tailWord_1762716
  simp only [CollatzResearch.WordTrace]
  refine ⟨32145767140994227385130001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42861022854658969846840001 32145767140994227385130001)
  ·
    refine ⟨24109325355745670538847501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32145767140994227385130001 24109325355745670538847501)
    ·
      refine ⟨9040997008404626452067813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24109325355745670538847501 9040997008404626452067813)
      ·
        refine ⟨1695186939075867459762715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9040997008404626452067813 1695186939075867459762715)
        ·
          refine ⟨2542780408613801189644073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1695186939075867459762715 2542780408613801189644073)
          ·
            refine ⟨1907085306460350892233055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2542780408613801189644073 1907085306460350892233055)
            ·
              refine ⟨2860627959690526338349583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1907085306460350892233055 2860627959690526338349583)
              ·
                refine ⟨4290941939535789507524375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2860627959690526338349583 4290941939535789507524375)
                ·
                  refine ⟨6436412909303684261286563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4290941939535789507524375 6436412909303684261286563)
                  ·
                    refine ⟨9654619363955526391929845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6436412909303684261286563 9654619363955526391929845)
                    ·
                      refine ⟨905120565370830599243423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9654619363955526391929845 905120565370830599243423)
                      ·
                        rfl

theorem cell23_1762716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1762716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762716 prefixEnd_1762716 := by exact prefixLift 1762716
  have htrace : WordTrace (prefixWord ++ tailWord_1762716) baseStart_1762716 baseEnd_1762716 := by
    simpa [prefixWord, tailWord_1762716, baseEnd_1762716] using wordTrace_append hprefix tailTrace_1762716
  have hstable : (prefixWord ++ tailWord_1762716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762716).length < 2 ^ (prefixWord ++ tailWord_1762716).sum := by decide
  have hdescent : baseEnd_1762716 < baseStart_1762716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762755 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 5]
def baseStart_1762755 : Nat := 118140960795 + 1762755 * 2 ^ 59
def prefixEnd_1762755 : Nat := 4983230072969 + 3 ^ 40 * 1762755 * 2
def baseEnd_1762755 : Nat := 905140591116355946655743

theorem tailTrace_1762755 : CollatzResearch.WordTrace tailWord_1762755 prefixEnd_1762755 905140591116355946655743 := by
  unfold tailWord_1762755
  simp only [CollatzResearch.WordTrace]
  refine ⟨64292956728847164430929719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42861971152564776287286479 64292956728847164430929719)
  ·
    refine ⟨96439435093270746646394579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64292956728847164430929719 96439435093270746646394579)
    ·
      refine ⟨144659152639906119969591869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96439435093270746646394579 144659152639906119969591869)
      ·
        refine ⟨54247182239964794988596951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144659152639906119969591869 54247182239964794988596951)
        ·
          refine ⟨81370773359947192482895427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54247182239964794988596951 81370773359947192482895427)
          ·
            refine ⟨122056160039920788724343141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81370773359947192482895427 122056160039920788724343141)
            ·
              refine ⟨22885530007485147885814339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122056160039920788724343141 22885530007485147885814339)
              ·
                refine ⟨34328295011227721828721509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22885530007485147885814339 34328295011227721828721509)
                ·
                  refine ⟨6436555314605197842885283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34328295011227721828721509 6436555314605197842885283)
                  ·
                    refine ⟨9654832971907796764327925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6436555314605197842885283 9654832971907796764327925)
                    ·
                      refine ⟨905140591116355946655743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9654832971907796764327925 905140591116355946655743)
                      ·
                        rfl

theorem cell23_1762755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_1762755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762755 prefixEnd_1762755 := by exact prefixLift 1762755
  have htrace : WordTrace (prefixWord ++ tailWord_1762755) baseStart_1762755 baseEnd_1762755 := by
    simpa [prefixWord, tailWord_1762755, baseEnd_1762755] using wordTrace_append hprefix tailTrace_1762755
  have hstable : (prefixWord ++ tailWord_1762755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762755).length < 2 ^ (prefixWord ++ tailWord_1762755).sum := by decide
  have hdescent : baseEnd_1762755 < baseStart_1762755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762756 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_1762756 : Nat := 118140960795 + 1762756 * 2 ^ 59
def prefixEnd_1762756 : Nat := 4983230072969 + 3 ^ 40 * 1762756 * 2
def baseEnd_1762756 : Nat := 905141104597010442743239

theorem tailTrace_1762756 : CollatzResearch.WordTrace tailWord_1762756 prefixEnd_1762756 905141104597010442743239 := by
  unfold tailWord_1762756
  simp only [CollatzResearch.WordTrace]
  refine ⟨32146496600921770800858061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42861995467895694401144081 32146496600921770800858061)
  ·
    refine ⟨12054936225345664050321773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32146496600921770800858061 12054936225345664050321773)
    ·
      refine ⟨4520601084504624018870665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12054936225345664050321773 4520601084504624018870665)
      ·
        refine ⟨3390450813378468014152999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4520601084504624018870665 3390450813378468014152999)
        ·
          refine ⟨5085676220067702021229499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3390450813378468014152999 5085676220067702021229499)
          ·
            refine ⟨7628514330101553031844249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5085676220067702021229499 7628514330101553031844249)
            ·
              refine ⟨5721385747576164773883187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7628514330101553031844249 5721385747576164773883187)
              ·
                refine ⟨8582078621364247160824781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5721385747576164773883187 8582078621364247160824781)
                ·
                  refine ⟨3218279483011592685309293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8582078621364247160824781 3218279483011592685309293)
                  ·
                    refine ⟨1206854806129347256990985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3218279483011592685309293 1206854806129347256990985)
                    ·
                      refine ⟨905141104597010442743239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1206854806129347256990985 905141104597010442743239)
                      ·
                        rfl

theorem cell23_1762756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_1762756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762756 prefixEnd_1762756 := by exact prefixLift 1762756
  have htrace : WordTrace (prefixWord ++ tailWord_1762756) baseStart_1762756 baseEnd_1762756 := by
    simpa [prefixWord, tailWord_1762756, baseEnd_1762756] using wordTrace_append hprefix tailTrace_1762756
  have hstable : (prefixWord ++ tailWord_1762756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762756).length < 2 ^ (prefixWord ++ tailWord_1762756).sum := by decide
  have hdescent : baseEnd_1762756 < baseStart_1762756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762792 : List Nat := [2, 1, 4, 1, 1, 2, 4, 1, 7]
def baseStart_1762792 : Nat := 118140960795 + 1762792 * 2 ^ 59
def prefixEnd_1762792 : Nat := 4983230072969 + 3 ^ 40 * 1762792 * 2
def baseEnd_1762792 : Nat := 100573287766730255765897

theorem tailTrace_1762792 : CollatzResearch.WordTrace tailWord_1762792 prefixEnd_1762792 100573287766730255765897 := by
  unfold tailWord_1762792
  simp only [CollatzResearch.WordTrace]
  refine ⟨32147153114856559875013315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42862870819808746500017753 32147153114856559875013315)
  ·
    refine ⟨48220729672284839812519973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32147153114856559875013315 48220729672284839812519973)
    ·
      refine ⟨9041386813553407464847495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48220729672284839812519973 9041386813553407464847495)
      ·
        refine ⟨13562080220330111197271243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9041386813553407464847495 13562080220330111197271243)
        ·
          refine ⟨20343120330495166795906865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13562080220330111197271243 20343120330495166795906865)
          ·
            refine ⟨15257340247871375096930149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20343120330495166795906865 15257340247871375096930149)
            ·
              refine ⟨2860751296475882830674403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15257340247871375096930149 2860751296475882830674403)
              ·
                refine ⟨4291126944713824246011605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2860751296475882830674403 4291126944713824246011605)
                ·
                  refine ⟨100573287766730255765897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4291126944713824246011605 100573287766730255765897)
                  ·
                    rfl

theorem cell23_1762792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 7].length) (baseStart_1762792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762792 prefixEnd_1762792 := by exact prefixLift 1762792
  have htrace : WordTrace (prefixWord ++ tailWord_1762792) baseStart_1762792 baseEnd_1762792 := by
    simpa [prefixWord, tailWord_1762792, baseEnd_1762792] using wordTrace_append hprefix tailTrace_1762792
  have hstable : (prefixWord ++ tailWord_1762792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762792).length < 2 ^ (prefixWord ++ tailWord_1762792).sum := by decide
  have hdescent : baseEnd_1762792 < baseStart_1762792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762815 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 7]
def baseStart_1762815 : Nat := 118140960795 + 1762815 * 2 ^ 59
def prefixEnd_1762815 : Nat := 4983230072969 + 3 ^ 40 * 1762815 * 2
def baseEnd_1762815 : Nat := 905171399955625711905467

theorem tailTrace_1762815 : CollatzResearch.WordTrace tailWord_1762815 prefixEnd_1762815 905171399955625711905467 := by
  unfold tailWord_1762815
  simp only [CollatzResearch.WordTrace]
  refine ⟨64295145108629794678113899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42863430072419863118742599 64295145108629794678113899)
  ·
    refine ⟨96442717662944692017170849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64295145108629794678113899 96442717662944692017170849)
    ·
      refine ⟨72332038247208519012878137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96442717662944692017170849 72332038247208519012878137)
      ·
        refine ⟨54249028685406389259658603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72332038247208519012878137 54249028685406389259658603)
        ·
          refine ⟨81373543028109583889487905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54249028685406389259658603 81373543028109583889487905)
          ·
            refine ⟨61030157271082187917115929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81373543028109583889487905 61030157271082187917115929)
            ·
              refine ⟨45772617953311640937836947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61030157271082187917115929 45772617953311640937836947)
              ·
                refine ⟨68658926929967461406755421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45772617953311640937836947 68658926929967461406755421)
                ·
                  refine ⟨25747097598737798027533283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68658926929967461406755421 25747097598737798027533283)
                  ·
                    refine ⟨38620646398106697041299925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25747097598737798027533283 38620646398106697041299925)
                    ·
                      refine ⟨905171399955625711905467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38620646398106697041299925 905171399955625711905467)
                      ·
                        rfl

theorem cell23_1762815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_1762815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762815 prefixEnd_1762815 := by exact prefixLift 1762815
  have htrace : WordTrace (prefixWord ++ tailWord_1762815) baseStart_1762815 baseEnd_1762815 := by
    simpa [prefixWord, tailWord_1762815, baseEnd_1762815] using wordTrace_append hprefix tailTrace_1762815
  have hstable : (prefixWord ++ tailWord_1762815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762815).length < 2 ^ (prefixWord ++ tailWord_1762815).sum := by decide
  have hdescent : baseEnd_1762815 < baseStart_1762815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762826 : List Nat := [3, 1, 2, 2, 2, 4, 1, 3, 5]
def baseStart_1762826 : Nat := 118140960795 + 1762826 * 2 ^ 59
def prefixEnd_1762826 : Nat := 4983230072969 + 3 ^ 40 * 1762826 * 2
def baseEnd_1762826 : Nat := 100575227582536129874213

theorem tailTrace_1762826 : CollatzResearch.WordTrace tailWord_1762826 prefixEnd_1762826 100575227582536129874213 := by
  unfold tailWord_1762826
  simp only [CollatzResearch.WordTrace]
  refine ⟨16073886577897485889191083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42863697541059962371176221 16073886577897485889191083)
  ·
    refine ⟨24110829866846228833786625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16073886577897485889191083 24110829866846228833786625)
    ·
      refine ⟨18083122400134671625339969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24110829866846228833786625 18083122400134671625339969)
      ·
        refine ⟨13562341800101003719004977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18083122400134671625339969 13562341800101003719004977)
        ·
          refine ⟨10171756350075752789253733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13562341800101003719004977 10171756350075752789253733)
          ·
            refine ⟨1907204315639203647985075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10171756350075752789253733 1907204315639203647985075)
            ·
              refine ⟨2860806473458805471977613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1907204315639203647985075 2860806473458805471977613)
              ·
                refine ⟨1072802427547052051991605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2860806473458805471977613 1072802427547052051991605)
                ·
                  refine ⟨100575227582536129874213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1072802427547052051991605 100575227582536129874213)
                  ·
                    rfl

theorem cell23_1762826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 5].length) (baseStart_1762826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762826 prefixEnd_1762826 := by exact prefixLift 1762826
  have htrace : WordTrace (prefixWord ++ tailWord_1762826) baseStart_1762826 baseEnd_1762826 := by
    simpa [prefixWord, tailWord_1762826, baseEnd_1762826] using wordTrace_append hprefix tailTrace_1762826
  have hstable : (prefixWord ++ tailWord_1762826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762826).length < 2 ^ (prefixWord ++ tailWord_1762826).sum := by decide
  have hdescent : baseEnd_1762826 < baseStart_1762826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762876 : List Nat := [2, 2, 2, 2, 4, 1, 2, 1, 2, 1, 4]
def baseStart_1762876 : Nat := 118140960795 + 1762876 * 2 ^ 59
def prefixEnd_1762876 : Nat := 4983230072969 + 3 ^ 40 * 1762876 * 2
def baseEnd_1762876 : Nat := 905202722275549973242687

theorem tailTrace_1762876 : CollatzResearch.WordTrace tailWord_1762876 prefixEnd_1762876 905202722275549973242687 := by
  unfold tailWord_1762876
  simp only [CollatzResearch.WordTrace]
  refine ⟨32148684980704401048042241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42864913307605868064056321 32148684980704401048042241)
  ·
    refine ⟨24111513735528300786031681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32148684980704401048042241 24111513735528300786031681)
    ·
      refine ⟨18083635301646225589523761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24111513735528300786031681 18083635301646225589523761)
      ·
        refine ⟨13562726476234669192142821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18083635301646225589523761 13562726476234669192142821)
        ·
          refine ⟨2543011214294000473526779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13562726476234669192142821 2543011214294000473526779)
          ·
            refine ⟨3814516821441000710290169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543011214294000473526779 3814516821441000710290169)
            ·
              refine ⟨2860887616080750532717627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3814516821441000710290169 2860887616080750532717627)
              ·
                refine ⟨4291331424121125799076441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2860887616080750532717627 4291331424121125799076441)
                ·
                  refine ⟨3218498568090844349307331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4291331424121125799076441 3218498568090844349307331)
                  ·
                    refine ⟨4827747852136266523960997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3218498568090844349307331 4827747852136266523960997)
                    ·
                      refine ⟨905202722275549973242687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4827747852136266523960997 905202722275549973242687)
                      ·
                        rfl

theorem cell23_1762876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_1762876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762876 prefixEnd_1762876 := by exact prefixLift 1762876
  have htrace : WordTrace (prefixWord ++ tailWord_1762876) baseStart_1762876 baseEnd_1762876 := by
    simpa [prefixWord, tailWord_1762876, baseEnd_1762876] using wordTrace_append hprefix tailTrace_1762876
  have hstable : (prefixWord ++ tailWord_1762876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762876).length < 2 ^ (prefixWord ++ tailWord_1762876).sum := by decide
  have hdescent : baseEnd_1762876 < baseStart_1762876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762879 : List Nat := [1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 3]
def baseStart_1762879 : Nat := 118140960795 + 1762879 * 2 ^ 59
def prefixEnd_1762879 : Nat := 4983230072969 + 3 ^ 40 * 1762879 * 2
def baseEnd_1762879 : Nat := 905204262717513461505173

theorem tailTrace_1762879 : CollatzResearch.WordTrace tailWord_1762879 prefixEnd_1762879 905204262717513461505173 := by
  unfold tailWord_1762879
  simp only [CollatzResearch.WordTrace]
  refine ⟨64297479380397933608443691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42864986253598622405629127 64297479380397933608443691)
  ·
    refine ⟨96446219070596900412665537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64297479380397933608443691 96446219070596900412665537)
    ·
      refine ⟨72334664302947675309499153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96446219070596900412665537 72334664302947675309499153)
      ·
        refine ⟨54250998227210756482124365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72334664302947675309499153 54250998227210756482124365)
        ·
          refine ⟨20344124335204033680796637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54250998227210756482124365 20344124335204033680796637)
          ·
            refine ⟨7629046625701512630298739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20344124335204033680796637 7629046625701512630298739)
            ·
              refine ⟨11443569938552268945448109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7629046625701512630298739 11443569938552268945448109)
              ·
                refine ⟨4291338726957100854543041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11443569938552268945448109 4291338726957100854543041)
                ·
                  refine ⟨3218504045217825640907281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4291338726957100854543041 3218504045217825640907281)
                  ·
                    refine ⟨2413878033913369230680461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3218504045217825640907281 2413878033913369230680461)
                    ·
                      refine ⟨905204262717513461505173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2413878033913369230680461 905204262717513461505173)
                      ·
                        rfl

theorem cell23_1762879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_1762879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762879 prefixEnd_1762879 := by exact prefixLift 1762879
  have htrace : WordTrace (prefixWord ++ tailWord_1762879) baseStart_1762879 baseEnd_1762879 := by
    simpa [prefixWord, tailWord_1762879, baseEnd_1762879] using wordTrace_append hprefix tailTrace_1762879
  have hstable : (prefixWord ++ tailWord_1762879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762879).length < 2 ^ (prefixWord ++ tailWord_1762879).sum := by decide
  have hdescent : baseEnd_1762879 < baseStart_1762879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762903 : List Nat := [1, 1, 3, 2, 2, 3, 4, 2, 1, 4]
def baseStart_1762903 : Nat := 118140960795 + 1762903 * 2 ^ 59
def prefixEnd_1762903 : Nat := 4983230072969 + 3 ^ 40 * 1762903 * 2
def baseEnd_1762903 : Nat := 301738862084407122535021

theorem tailTrace_1762903 : CollatzResearch.WordTrace tailWord_1762903 prefixEnd_1762903 301738862084407122535021 := by
  unfold tailWord_1762903
  simp only [CollatzResearch.WordTrace]
  refine ⟨64298354732310985707317363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42865569821540657138211575 64298354732310985707317363)
  ·
    refine ⟨96447532098466478560976045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64298354732310985707317363 96447532098466478560976045)
    ·
      refine ⟨36167824536924929460366017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96447532098466478560976045 36167824536924929460366017)
      ·
        refine ⟨27125868402693697095274513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36167824536924929460366017 27125868402693697095274513)
        ·
          refine ⟨20344401302020272821455885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27125868402693697095274513 20344401302020272821455885)
          ·
            refine ⟨7629150488257602308045957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20344401302020272821455885 7629150488257602308045957)
            ·
              refine ⟨1430465716548300432758617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7629150488257602308045957 1430465716548300432758617)
              ·
                refine ⟨1072849287411225324568963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1430465716548300432758617 1072849287411225324568963)
                ·
                  refine ⟨1609273931116837986853445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1072849287411225324568963 1609273931116837986853445)
                  ·
                    refine ⟨301738862084407122535021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1609273931116837986853445 301738862084407122535021)
                    ·
                      rfl

theorem cell23_1762903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 1, 4].length) (baseStart_1762903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762903 prefixEnd_1762903 := by exact prefixLift 1762903
  have htrace : WordTrace (prefixWord ++ tailWord_1762903) baseStart_1762903 baseEnd_1762903 := by
    simpa [prefixWord, tailWord_1762903, baseEnd_1762903] using wordTrace_append hprefix tailTrace_1762903
  have hstable : (prefixWord ++ tailWord_1762903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762903).length < 2 ^ (prefixWord ++ tailWord_1762903).sum := by decide
  have hdescent : baseEnd_1762903 < baseStart_1762903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762969 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 3, 2, 3]
def baseStart_1762969 : Nat := 118140960795 + 1762969 * 2 ^ 59
def prefixEnd_1762969 : Nat := 4983230072969 + 3 ^ 40 * 1762969 * 2
def baseEnd_1762969 : Nat := 905250475976418109379759

theorem tailTrace_1762969 : CollatzResearch.WordTrace tailWord_1762969 prefixEnd_1762969 905250475976418109379759 := by
  unfold tailWord_1762969
  simp only [CollatzResearch.WordTrace]
  refine ⟨64300761950071878979219961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42867174633381252652813307 64300761950071878979219961)
  ·
    refine ⟨48225571462553909234414971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64300761950071878979219961 48225571462553909234414971)
    ·
      refine ⟨72338357193830863851622457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48225571462553909234414971 72338357193830863851622457)
      ·
        refine ⟨54253767895373147888716843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72338357193830863851622457 54253767895373147888716843)
        ·
          refine ⟨81380651843059721833075265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54253767895373147888716843 81380651843059721833075265)
          ·
            refine ⟨61035488882294791374806449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81380651843059721833075265 61035488882294791374806449)
            ·
              refine ⟨45776616661721093531104837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61035488882294791374806449 45776616661721093531104837)
              ·
                refine ⟨8583115624072705037082157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45776616661721093531104837 8583115624072705037082157)
                ·
                  refine ⟨3218668359027264388905809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8583115624072705037082157 3218668359027264388905809)
                  ·
                    refine ⟨2414001269270448291679357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3218668359027264388905809 2414001269270448291679357)
                    ·
                      refine ⟨905250475976418109379759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2414001269270448291679357 905250475976418109379759)
                      ·
                        rfl

theorem cell23_1762969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_1762969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762969 prefixEnd_1762969 := by exact prefixLift 1762969
  have htrace : WordTrace (prefixWord ++ tailWord_1762969) baseStart_1762969 baseEnd_1762969 := by
    simpa [prefixWord, tailWord_1762969, baseEnd_1762969] using wordTrace_append hprefix tailTrace_1762969
  have hstable : (prefixWord ++ tailWord_1762969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762969).length < 2 ^ (prefixWord ++ tailWord_1762969).sum := by decide
  have hdescent : baseEnd_1762969 < baseStart_1762969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762976 : List Nat := [2, 1, 1, 4, 3, 3, 1, 1, 1, 6]
def baseStart_1762976 : Nat := 118140960795 + 1762976 * 2 ^ 59
def prefixEnd_1762976 : Nat := 4983230072969 + 3 ^ 40 * 1762976 * 2
def baseEnd_1762976 : Nat := 301751356780333193997409

theorem tailTrace_1762976 : CollatzResearch.WordTrace tailWord_1762976 prefixEnd_1762976 301751356780333193997409 := by
  unfold tailWord_1762976
  simp only [CollatzResearch.WordTrace]
  refine ⟨32150508630523259587362391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42867344840697679449816521 32150508630523259587362391)
  ·
    refine ⟨48225762945784889381043587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32150508630523259587362391 48225762945784889381043587)
    ·
      refine ⟨72338644418677334071565381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48225762945784889381043587 72338644418677334071565381)
      ·
        refine ⟨13563495828502000138418509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72338644418677334071565381 13563495828502000138418509)
        ·
          refine ⟨5086310935688250051906941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13563495828502000138418509 5086310935688250051906941)
          ·
            refine ⟨1907366600883093769465103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5086310935688250051906941 1907366600883093769465103)
            ·
              refine ⟨2861049901324640654197655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1907366600883093769465103 2861049901324640654197655)
              ·
                refine ⟨4291574851986960981296483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2861049901324640654197655 4291574851986960981296483)
                ·
                  refine ⟨6437362277980441471944725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4291574851986960981296483 6437362277980441471944725)
                  ·
                    refine ⟨301751356780333193997409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6437362277980441471944725 301751356780333193997409)
                    ·
                      rfl

theorem cell23_1762976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 1, 6].length) (baseStart_1762976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762976 prefixEnd_1762976 := by exact prefixLift 1762976
  have htrace : WordTrace (prefixWord ++ tailWord_1762976) baseStart_1762976 baseEnd_1762976 := by
    simpa [prefixWord, tailWord_1762976, baseEnd_1762976] using wordTrace_append hprefix tailTrace_1762976
  have hstable : (prefixWord ++ tailWord_1762976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762976).length < 2 ^ (prefixWord ++ tailWord_1762976).sum := by decide
  have hdescent : baseEnd_1762976 < baseStart_1762976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762989 : List Nat := [1, 5, 2, 1, 1, 1, 3, 9]
def baseStart_1762989 : Nat := 118140960795 + 1762989 * 2 ^ 59
def prefixEnd_1762989 : Nat := 4983230072969 + 3 ^ 40 * 1762989 * 2
def baseEnd_1762989 : Nat := 33528175762574371523321

theorem tailTrace_1762989 : CollatzResearch.WordTrace tailWord_1762989 prefixEnd_1762989 33528175762574371523321 := by
  unfold tailWord_1762989
  simp only [CollatzResearch.WordTrace]
  refine ⟨64301491409999422394948021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42867660939999614929965347 64301491409999422394948021)
  ·
    refine ⟨6028264819687445849526377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64301491409999422394948021 6028264819687445849526377)
    ·
      refine ⟨4521198614765584387144783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6028264819687445849526377 4521198614765584387144783)
      ·
        refine ⟨6781797922148376580717175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4521198614765584387144783 6781797922148376580717175)
        ·
          refine ⟨10172696883222564871075763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6781797922148376580717175 10172696883222564871075763)
          ·
            refine ⟨15259045324833847306613645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10172696883222564871075763 15259045324833847306613645)
            ·
              refine ⟨5722141996812692739980117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15259045324833847306613645 5722141996812692739980117)
              ·
                refine ⟨33528175762574371523321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5722141996812692739980117 33528175762574371523321)
                ·
                  rfl

theorem cell23_1762989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 9].length) (baseStart_1762989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762989 prefixEnd_1762989 := by exact prefixLift 1762989
  have htrace : WordTrace (prefixWord ++ tailWord_1762989) baseStart_1762989 baseEnd_1762989 := by
    simpa [prefixWord, tailWord_1762989, baseEnd_1762989] using wordTrace_append hprefix tailTrace_1762989
  have hstable : (prefixWord ++ tailWord_1762989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762989).length < 2 ^ (prefixWord ++ tailWord_1762989).sum := by decide
  have hdescent : baseEnd_1762989 < baseStart_1762989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763016 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 4, 1, 3]
def baseStart_1763016 : Nat := 118140960795 + 1763016 * 2 ^ 59
def prefixEnd_1763016 : Nat := 4983230072969 + 3 ^ 40 * 1763016 * 2
def baseEnd_1763016 : Nat := 905274609567179425492043

theorem tailTrace_1763016 : CollatzResearch.WordTrace tailWord_1763016 prefixEnd_1763016 905274609567179425492043 := by
  unfold tailWord_1763016
  simp only [CollatzResearch.WordTrace]
  refine ⟨32151238090450803003090451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42868317453934404004120601 32151238090450803003090451)
  ·
    refine ⟨48226857135676204504635677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32151238090450803003090451 48226857135676204504635677)
    ·
      refine ⟨18085071425878576689238379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48226857135676204504635677 18085071425878576689238379)
      ·
        refine ⟨27127607138817865033857569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18085071425878576689238379 27127607138817865033857569)
        ·
          refine ⟨20345705354113398775393177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27127607138817865033857569 20345705354113398775393177)
          ·
            refine ⟨15259279015585049081544883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20345705354113398775393177 15259279015585049081544883)
            ·
              refine ⟨22888918523377573622317325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15259279015585049081544883 22888918523377573622317325)
              ·
                refine ⟨8583344446266590108368997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22888918523377573622317325 8583344446266590108368997)
                ·
                  refine ⟨1609377083674985645319187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8583344446266590108368997 1609377083674985645319187)
                  ·
                    refine ⟨2414065625512478467978781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1609377083674985645319187 2414065625512478467978781)
                    ·
                      refine ⟨905274609567179425492043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2414065625512478467978781 905274609567179425492043)
                      ·
                        rfl

theorem cell23_1763016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_1763016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763016 prefixEnd_1763016 := by exact prefixLift 1763016
  have htrace : WordTrace (prefixWord ++ tailWord_1763016) baseStart_1763016 baseEnd_1763016 := by
    simpa [prefixWord, tailWord_1763016, baseEnd_1763016] using wordTrace_append hprefix tailTrace_1763016
  have hstable : (prefixWord ++ tailWord_1763016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763016).length < 2 ^ (prefixWord ++ tailWord_1763016).sum := by decide
  have hdescent : baseEnd_1763016 < baseStart_1763016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763033 : List Nat := [1, 2, 1, 2, 3, 4, 1, 3, 2, 1, 3]
def baseStart_1763033 : Nat := 118140960795 + 1763033 * 2 ^ 59
def prefixEnd_1763033 : Nat := 4983230072969 + 3 ^ 40 * 1763033 * 2
def baseEnd_1763033 : Nat := 905283338738305858979465

theorem tailTrace_1763033 : CollatzResearch.WordTrace tailWord_1763033 prefixEnd_1763033 905283338738305858979465 := by
  unfold tailWord_1763033
  simp only [CollatzResearch.WordTrace]
  refine ⟨64303096221840017909549753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42868730814560011939699835 64303096221840017909549753)
  ·
    refine ⟨48227322166380013432162315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64303096221840017909549753 48227322166380013432162315)
    ·
      refine ⟨72340983249570020148243473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48227322166380013432162315 72340983249570020148243473)
      ·
        refine ⟨54255737437177515111182605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72340983249570020148243473 54255737437177515111182605)
        ·
          refine ⟨20345901538941568166693477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54255737437177515111182605 20345901538941568166693477)
          ·
            refine ⟨3814856538551544031255027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20345901538941568166693477 3814856538551544031255027)
            ·
              refine ⟨5722284807827316046882541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3814856538551544031255027 5722284807827316046882541)
              ·
                refine ⟨2145856802935243517580953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5722284807827316046882541 2145856802935243517580953)
                ·
                  refine ⟨1609392602201432638185715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2145856802935243517580953 1609392602201432638185715)
                  ·
                    refine ⟨2414088903302148957278573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1609392602201432638185715 2414088903302148957278573)
                    ·
                      refine ⟨905283338738305858979465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2414088903302148957278573 905283338738305858979465)
                      ·
                        rfl

theorem cell23_1763033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 1, 3].length) (baseStart_1763033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763033 prefixEnd_1763033 := by exact prefixLift 1763033
  have htrace : WordTrace (prefixWord ++ tailWord_1763033) baseStart_1763033 baseEnd_1763033 := by
    simpa [prefixWord, tailWord_1763033, baseEnd_1763033] using wordTrace_append hprefix tailTrace_1763033
  have hstable : (prefixWord ++ tailWord_1763033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763033).length < 2 ^ (prefixWord ++ tailWord_1763033).sum := by decide
  have hdescent : baseEnd_1763033 < baseStart_1763033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763037 : List Nat := [1, 4, 3, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1763037 : Nat := 118140960795 + 1763037 * 2 ^ 59
def prefixEnd_1763037 : Nat := 4983230072969 + 3 ^ 40 * 1763037 * 2
def baseEnd_1763037 : Nat := 905285392660923843329447

theorem tailTrace_1763037 : CollatzResearch.WordTrace tailWord_1763037 prefixEnd_1763037 905285392660923843329447 := by
  unfold tailWord_1763037
  simp only [CollatzResearch.WordTrace]
  refine ⟨64303242113825526592695365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42868828075883684395130243 64303242113825526592695365)
  ·
    refine ⟨12056857896342286236130381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64303242113825526592695365 12056857896342286236130381)
    ·
      refine ⟨4521321711128357338548893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12056857896342286236130381 4521321711128357338548893)
      ·
        refine ⟨1695495641673134001955835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4521321711128357338548893 1695495641673134001955835)
        ·
          refine ⟨2543243462509701002933753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1695495641673134001955835 2543243462509701002933753)
          ·
            refine ⟨1907432596882275752200315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2543243462509701002933753 1907432596882275752200315)
            ·
              refine ⟨2861148895323413628300473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1907432596882275752200315 2861148895323413628300473)
              ·
                refine ⟨2145861671492560221225355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2861148895323413628300473 2145861671492560221225355)
                ·
                  refine ⟨3218792507238840331838033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145861671492560221225355 3218792507238840331838033)
                  ·
                    refine ⟨2414094380429130248878525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3218792507238840331838033 2414094380429130248878525)
                    ·
                      refine ⟨905285392660923843329447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2414094380429130248878525 905285392660923843329447)
                      ·
                        rfl

theorem cell23_1763037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1763037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763037 prefixEnd_1763037 := by exact prefixLift 1763037
  have htrace : WordTrace (prefixWord ++ tailWord_1763037) baseStart_1763037 baseEnd_1763037 := by
    simpa [prefixWord, tailWord_1763037, baseEnd_1763037] using wordTrace_append hprefix tailTrace_1763037
  have hstable : (prefixWord ++ tailWord_1763037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763037).length < 2 ^ (prefixWord ++ tailWord_1763037).sum := by decide
  have hdescent : baseEnd_1763037 < baseStart_1763037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763059 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 5]
def baseStart_1763059 : Nat := 118140960795 + 1763059 * 2 ^ 59
def prefixEnd_1763059 : Nat := 4983230072969 + 3 ^ 40 * 1763059 * 2
def baseEnd_1763059 : Nat := 905296689235322757254345

theorem tailTrace_1763059 : CollatzResearch.WordTrace tailWord_1763059 prefixEnd_1763059 905296689235322757254345 := by
  unfold tailWord_1763059
  simp only [CollatzResearch.WordTrace]
  refine ⟨64304044519745824349996231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42869363013163882899997487 64304044519745824349996231)
  ·
    refine ⟨96456066779618736524994347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64304044519745824349996231 96456066779618736524994347)
    ·
      refine ⟨144684100169428104787491521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96456066779618736524994347 144684100169428104787491521)
      ·
        refine ⟨108513075127071078590618641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144684100169428104787491521 108513075127071078590618641)
        ·
          refine ⟨81384806345303308942963981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108513075127071078590618641 81384806345303308942963981)
          ·
            refine ⟨30519302379488740853611493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81384806345303308942963981 30519302379488740853611493)
            ·
              refine ⟨5722369196154138910052155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30519302379488740853611493 5722369196154138910052155)
              ·
                refine ⟨8583553794231208365078233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5722369196154138910052155 8583553794231208365078233)
                ·
                  refine ⟨6437665345673406273808675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8583553794231208365078233 6437665345673406273808675)
                  ·
                    refine ⟨9656498018510109410713013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6437665345673406273808675 9656498018510109410713013)
                    ·
                      refine ⟨905296689235322757254345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9656498018510109410713013 905296689235322757254345)
                      ·
                        rfl

theorem cell23_1763059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 5].length) (baseStart_1763059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763059 prefixEnd_1763059 := by exact prefixLift 1763059
  have htrace : WordTrace (prefixWord ++ tailWord_1763059) baseStart_1763059 baseEnd_1763059 := by
    simpa [prefixWord, tailWord_1763059, baseEnd_1763059] using wordTrace_append hprefix tailTrace_1763059
  have hstable : (prefixWord ++ tailWord_1763059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763059).length < 2 ^ (prefixWord ++ tailWord_1763059).sum := by decide
  have hdescent : baseEnd_1763059 < baseStart_1763059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763073 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 4, 2, 2]
def baseStart_1763073 : Nat := 118140960795 + 1763073 * 2 ^ 59
def prefixEnd_1763073 : Nat := 4983230072969 + 3 ^ 40 * 1763073 * 2
def baseEnd_1763073 : Nat := 905303877964485702479281

theorem tailTrace_1763073 : CollatzResearch.WordTrace tailWord_1763073 prefixEnd_1763073 905303877964485702479281 := by
  unfold tailWord_1763073
  simp only [CollatzResearch.WordTrace]
  refine ⟨64304555141695104741005873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42869703427796736494003915 64304555141695104741005873)
  ·
    refine ⟨48228416356271328555754405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64304555141695104741005873 48228416356271328555754405)
    ·
      refine ⟨9042828066800874104203951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48228416356271328555754405 9042828066800874104203951)
      ·
        refine ⟨13564242100201311156305927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9042828066800874104203951 13564242100201311156305927)
        ·
          refine ⟨20346363150301966734458891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13564242100201311156305927 20346363150301966734458891)
          ·
            refine ⟨30519544725452950101688337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20346363150301966734458891 30519544725452950101688337)
            ·
              refine ⟨22889658544089712576266253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30519544725452950101688337 22889658544089712576266253)
              ·
                refine ⟨8583621954033642216099845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22889658544089712576266253 8583621954033642216099845)
                ·
                  refine ⟨1609429116381307915518721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8583621954033642216099845 1609429116381307915518721)
                  ·
                    refine ⟨1207071837285980936639041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1609429116381307915518721 1207071837285980936639041)
                    ·
                      refine ⟨905303877964485702479281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1207071837285980936639041 905303877964485702479281)
                      ·
                        rfl

theorem cell23_1763073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_1763073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763073 prefixEnd_1763073 := by exact prefixLift 1763073
  have htrace : WordTrace (prefixWord ++ tailWord_1763073) baseStart_1763073 baseEnd_1763073 := by
    simpa [prefixWord, tailWord_1763073, baseEnd_1763073] using wordTrace_append hprefix tailTrace_1763073
  have hstable : (prefixWord ++ tailWord_1763073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763073).length < 2 ^ (prefixWord ++ tailWord_1763073).sum := by decide
  have hdescent : baseEnd_1763073 < baseStart_1763073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763076 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_1763076 : Nat := 118140960795 + 1763076 * 2 ^ 59
def prefixEnd_1763076 : Nat := 4983230072969 + 3 ^ 40 * 1763076 * 2
def baseEnd_1763076 : Nat := 905305418406449190741767

theorem tailTrace_1763076 : CollatzResearch.WordTrace tailWord_1763076 prefixEnd_1763076 905305418406449190741767 := by
  unfold tailWord_1763076
  simp only [CollatzResearch.WordTrace]
  refine ⟨32152332280342118126682541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42869776373789490835576721 32152332280342118126682541)
  ·
    refine ⟨12057124605128294297505953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32152332280342118126682541 12057124605128294297505953)
    ·
      refine ⟨9042843453846220723129465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12057124605128294297505953 9042843453846220723129465)
      ·
        refine ⟨6782132590384665542347099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9042843453846220723129465 6782132590384665542347099)
        ·
          refine ⟨10173198885576998313520649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6782132590384665542347099 10173198885576998313520649)
          ·
            refine ⟨7629899164182748735140487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10173198885576998313520649 7629899164182748735140487)
            ·
              refine ⟨11444848746274123102710731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7629899164182748735140487 11444848746274123102710731)
              ·
                refine ⟨17167273119411184654066097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11444848746274123102710731 17167273119411184654066097)
                ·
                  refine ⟨12875454839558388490549573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17167273119411184654066097 12875454839558388490549573)
                  ·
                    refine ⟨2414147782417197841978045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12875454839558388490549573 2414147782417197841978045)
                    ·
                      refine ⟨905305418406449190741767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2414147782417197841978045 905305418406449190741767)
                      ·
                        rfl

theorem cell23_1763076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_1763076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763076 prefixEnd_1763076 := by exact prefixLift 1763076
  have htrace : WordTrace (prefixWord ++ tailWord_1763076) baseStart_1763076 baseEnd_1763076 := by
    simpa [prefixWord, tailWord_1763076, baseEnd_1763076] using wordTrace_append hprefix tailTrace_1763076
  have hstable : (prefixWord ++ tailWord_1763076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763076).length < 2 ^ (prefixWord ++ tailWord_1763076).sum := by decide
  have hdescent : baseEnd_1763076 < baseStart_1763076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763090 : List Nat := [3, 2, 4, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_1763090 : Nat := 118140960795 + 1763090 * 2 ^ 59
def prefixEnd_1763090 : Nat := 4983230072969 + 3 ^ 40 * 1763090 * 2
def baseEnd_1763090 : Nat := 905312607135612135966703

theorem tailTrace_1763090 : CollatzResearch.WordTrace tailWord_1763090 prefixEnd_1763090 905312607135612135966703 := by
  unfold tailWord_1763090
  simp only [CollatzResearch.WordTrace]
  refine ⟨16076293795658379161093681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42870116788422344429583149 16076293795658379161093681)
  ·
    refine ⟨12057220346743784370820261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16076293795658379161093681 12057220346743784370820261)
    ·
      refine ⟨2260728815014459569528799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12057220346743784370820261 2260728815014459569528799)
      ·
        refine ⟨3391093222521689354293199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2260728815014459569528799 3391093222521689354293199)
        ·
          refine ⟨5086639833782534031439799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3391093222521689354293199 5086639833782534031439799)
          ·
            refine ⟨7629959750673801047159699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5086639833782534031439799 7629959750673801047159699)
            ·
              refine ⟨11444939626010701570739549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7629959750673801047159699 11444939626010701570739549)
              ·
                refine ⟨4291852359754013089027331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11444939626010701570739549 4291852359754013089027331)
                ·
                  refine ⟨6437778539631019633540997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4291852359754013089027331 6437778539631019633540997)
                  ·
                    refine ⟨1207083476180816181288937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6437778539631019633540997 1207083476180816181288937)
                    ·
                      refine ⟨905312607135612135966703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1207083476180816181288937 905312607135612135966703)
                      ·
                        rfl

theorem cell23_1763090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_1763090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763090 prefixEnd_1763090 := by exact prefixLift 1763090
  have htrace : WordTrace (prefixWord ++ tailWord_1763090) baseStart_1763090 baseEnd_1763090 := by
    simpa [prefixWord, tailWord_1763090, baseEnd_1763090] using wordTrace_append hprefix tailTrace_1763090
  have hstable : (prefixWord ++ tailWord_1763090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763090).length < 2 ^ (prefixWord ++ tailWord_1763090).sum := by decide
  have hdescent : baseEnd_1763090 < baseStart_1763090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763106 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_1763106 : Nat := 118140960795 + 1763106 * 2 ^ 59
def prefixEnd_1763106 : Nat := 4983230072969 + 3 ^ 40 * 1763106 * 2
def baseEnd_1763106 : Nat := 905320822826084073366629

theorem tailTrace_1763106 : CollatzResearch.WordTrace tailWord_1763106 prefixEnd_1763106 905320822826084073366629 := by
  unfold tailWord_1763106
  simp only [CollatzResearch.WordTrace]
  refine ⟨16076439687643887844239293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42870505833717034251304781 16076439687643887844239293)
  ·
    refine ⟨6028664882866457941589735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16076439687643887844239293 6028664882866457941589735)
    ·
      refine ⟨9042997324299686912384603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6028664882866457941589735 9042997324299686912384603)
      ·
        refine ⟨13564495986449530368576905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9042997324299686912384603 13564495986449530368576905)
        ·
          refine ⟨10173371989837147776432679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13564495986449530368576905 10173371989837147776432679)
          ·
            refine ⟨15260057984755721664649019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10173371989837147776432679 15260057984755721664649019)
            ·
              refine ⟨22890086977133582496973529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15260057984755721664649019 22890086977133582496973529)
              ·
                refine ⟨17167565232850186872730147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22890086977133582496973529 17167565232850186872730147)
                ·
                  refine ⟨25751347849275280309095221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17167565232850186872730147 25751347849275280309095221)
                  ·
                    refine ⟨2414188860869557528977677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25751347849275280309095221 2414188860869557528977677)
                    ·
                      refine ⟨905320822826084073366629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2414188860869557528977677 905320822826084073366629)
                      ·
                        rfl

theorem cell23_1763106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_1763106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763106 prefixEnd_1763106 := by exact prefixLift 1763106
  have htrace : WordTrace (prefixWord ++ tailWord_1763106) baseStart_1763106 baseEnd_1763106 := by
    simpa [prefixWord, tailWord_1763106, baseEnd_1763106] using wordTrace_append hprefix tailTrace_1763106
  have hstable : (prefixWord ++ tailWord_1763106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763106).length < 2 ^ (prefixWord ++ tailWord_1763106).sum := by decide
  have hdescent : baseEnd_1763106 < baseStart_1763106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763124 : List Nat := [2, 5, 1, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_1763124 : Nat := 118140960795 + 1763124 * 2 ^ 59
def prefixEnd_1763124 : Nat := 4983230072969 + 3 ^ 40 * 1763124 * 2
def baseEnd_1763124 : Nat := 905330065477865002941547

theorem tailTrace_1763124 : CollatzResearch.WordTrace tailWord_1763124 prefixEnd_1763124 905330065477865002941547 := by
  unfold tailWord_1763124
  simp only [CollatzResearch.WordTrace]
  refine ⟨32153207632255170225556213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42870943509673560300741617 32153207632255170225556213)
  ·
    refine ⟨3014363215523922208645895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32153207632255170225556213 3014363215523922208645895)
    ·
      refine ⟨4521544823285883312968843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3014363215523922208645895 4521544823285883312968843)
      ·
        refine ⟨6782317234928824969453265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4521544823285883312968843 6782317234928824969453265)
        ·
          refine ⟨5086737926196618727089949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6782317234928824969453265 5086737926196618727089949)
          ·
            refine ⟨1907526722323732022658731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5086737926196618727089949 1907526722323732022658731)
            ·
              refine ⟨2861290083485598033988097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1907526722323732022658731 2861290083485598033988097)
              ·
                refine ⟨2145967562614198525491073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2861290083485598033988097 2145967562614198525491073)
                ·
                  refine ⟨1609475671960648894118305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2145967562614198525491073 1609475671960648894118305)
                  ·
                    refine ⟨1207106753970486670588729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1609475671960648894118305 1207106753970486670588729)
                    ·
                      refine ⟨905330065477865002941547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1207106753970486670588729 905330065477865002941547)
                      ·
                        rfl

theorem cell23_1763124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_1763124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763124 prefixEnd_1763124 := by exact prefixLift 1763124
  have htrace : WordTrace (prefixWord ++ tailWord_1763124) baseStart_1763124 baseEnd_1763124 := by
    simpa [prefixWord, tailWord_1763124, baseEnd_1763124] using wordTrace_append hprefix tailTrace_1763124
  have hstable : (prefixWord ++ tailWord_1763124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763124).length < 2 ^ (prefixWord ++ tailWord_1763124).sum := by decide
  have hdescent : baseEnd_1763124 < baseStart_1763124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763169 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 10]
def baseStart_1763169 : Nat := 118140960795 + 1763169 * 2 ^ 59
def prefixEnd_1763169 : Nat := 4983230072969 + 3 ^ 40 * 1763169 * 2
def baseEnd_1763169 : Nat := 100594796900813036319871

theorem tailTrace_1763169 : CollatzResearch.WordTrace tailWord_1763169 prefixEnd_1763169 100594796900813036319871 := by
  unfold tailWord_1763169
  simp only [CollatzResearch.WordTrace]
  refine ⟨64308056549347313136500561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42872037699564875424333707 64308056549347313136500561)
  ·
    refine ⟨48231042412010484852375421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64308056549347313136500561 48231042412010484852375421)
    ·
      refine ⟨18086640904503931819640783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48231042412010484852375421 18086640904503931819640783)
      ·
        refine ⟨27129961356755897729461175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18086640904503931819640783 27129961356755897729461175)
        ·
          refine ⟨40694942035133846594191763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27129961356755897729461175 40694942035133846594191763)
          ·
            refine ⟨61042413052700769891287645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40694942035133846594191763 61042413052700769891287645)
            ·
              refine ⟨22890904894762788709232867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61042413052700769891287645 22890904894762788709232867)
              ·
                refine ⟨34336357342144183063849301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22890904894762788709232867 34336357342144183063849301)
                ·
                  refine ⟨100594796900813036319871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 34336357342144183063849301 100594796900813036319871)
                  ·
                    rfl

theorem cell23_1763169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 10].length) (baseStart_1763169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763169 prefixEnd_1763169 := by exact prefixLift 1763169
  have htrace : WordTrace (prefixWord ++ tailWord_1763169) baseStart_1763169 baseEnd_1763169 := by
    simpa [prefixWord, tailWord_1763169, baseEnd_1763169] using wordTrace_append hprefix tailTrace_1763169
  have hstable : (prefixWord ++ tailWord_1763169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763169).length < 2 ^ (prefixWord ++ tailWord_1763169).sum := by decide
  have hdescent : baseEnd_1763169 < baseStart_1763169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763186 : List Nat := [3, 2, 1, 2, 1, 1, 1, 6, 6]
def baseStart_1763186 : Nat := 118140960795 + 1763186 * 2 ^ 59
def prefixEnd_1763186 : Nat := 4983230072969 + 3 ^ 40 * 1763186 * 2
def baseEnd_1763186 : Nat := 100595766808715973374029

theorem tailTrace_1763186 : CollatzResearch.WordTrace tailWord_1763186 prefixEnd_1763186 100595766808715973374029 := by
  unfold tailWord_1763186
  simp only [CollatzResearch.WordTrace]
  refine ⟨16077169147571431259967353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42872451060190483359912941 16077169147571431259967353)
  ·
    refine ⟨12057876860678573444975515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16077169147571431259967353 12057876860678573444975515)
    ·
      refine ⟨18086815291017860167463273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12057876860678573444975515 18086815291017860167463273)
      ·
        refine ⟨13565111468263395125597455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18086815291017860167463273 13565111468263395125597455)
        ·
          refine ⟨20347667202395092688396183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13565111468263395125597455 20347667202395092688396183)
          ·
            refine ⟨30521500803592639032594275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20347667202395092688396183 30521500803592639032594275)
            ·
              refine ⟨45782251205388958548891413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30521500803592639032594275 45782251205388958548891413)
              ·
                refine ⟨2146043025252607431979285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45782251205388958548891413 2146043025252607431979285)
                ·
                  refine ⟨100595766808715973374029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2146043025252607431979285 100595766808715973374029)
                  ·
                    rfl

theorem cell23_1763186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_1763186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763186 prefixEnd_1763186 := by exact prefixLift 1763186
  have htrace : WordTrace (prefixWord ++ tailWord_1763186) baseStart_1763186 baseEnd_1763186 := by
    simpa [prefixWord, tailWord_1763186, baseEnd_1763186] using wordTrace_append hprefix tailTrace_1763186
  have hstable : (prefixWord ++ tailWord_1763186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763186).length < 2 ^ (prefixWord ++ tailWord_1763186).sum := by decide
  have hdescent : baseEnd_1763186 < baseStart_1763186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763199 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 2, 9]
def baseStart_1763199 : Nat := 118140960795 + 1763199 * 2 ^ 59
def prefixEnd_1763199 : Nat := 4983230072969 + 3 ^ 40 * 1763199 * 2
def baseEnd_1763199 : Nat := 301789525508984069834567

theorem tailTrace_1763199 : CollatzResearch.WordTrace tailWord_1763199 prefixEnd_1763199 301789525508984069834567 := by
  unfold tailWord_1763199
  simp only [CollatzResearch.WordTrace]
  refine ⟨64309150739238628260092651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42872767159492418840061767 64309150739238628260092651)
  ·
    refine ⟨96463726108857942390138977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64309150739238628260092651 96463726108857942390138977)
    ·
      refine ⟨72347794581643456792604233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96463726108857942390138977 72347794581643456792604233)
      ·
        refine ⟨54260845936232592594453175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72347794581643456792604233 54260845936232592594453175)
        ·
          refine ⟨81391268904348888891679763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54260845936232592594453175 81391268904348888891679763)
          ·
            refine ⟨122086903356523333337519645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81391268904348888891679763 122086903356523333337519645)
            ·
              refine ⟨45782588758696250001569867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122086903356523333337519645 45782588758696250001569867)
              ·
                refine ⟨68673883138044375002354801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45782588758696250001569867 68673883138044375002354801)
                ·
                  refine ⟨51505412353533281251766101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68673883138044375002354801 51505412353533281251766101)
                  ·
                    refine ⟨301789525508984069834567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 51505412353533281251766101 301789525508984069834567)
                    ·
                      rfl

theorem cell23_1763199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 9].length) (baseStart_1763199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763199 prefixEnd_1763199 := by exact prefixLift 1763199
  have htrace : WordTrace (prefixWord ++ tailWord_1763199) baseStart_1763199 baseEnd_1763199 := by
    simpa [prefixWord, tailWord_1763199, baseEnd_1763199] using wordTrace_append hprefix tailTrace_1763199
  have hstable : (prefixWord ++ tailWord_1763199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763199).length < 2 ^ (prefixWord ++ tailWord_1763199).sum := by decide
  have hdescent : baseEnd_1763199 < baseStart_1763199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763203 : List Nat := [1, 1, 1, 3, 4, 2, 4, 1, 6]
def baseStart_1763203 : Nat := 118140960795 + 1763203 * 2 ^ 59
def prefixEnd_1763203 : Nat := 4983230072969 + 3 ^ 40 * 1763203 * 2
def baseEnd_1763203 : Nat := 100596736716618910428187

theorem tailTrace_1763203 : CollatzResearch.WordTrace tailWord_1763203 prefixEnd_1763203 100596736716618910428187 := by
  unfold tailWord_1763203
  simp only [CollatzResearch.WordTrace]
  refine ⟨64309296631224136943238263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42872864420816091295492175 64309296631224136943238263)
  ·
    refine ⟨96463944946836205414857395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64309296631224136943238263 96463944946836205414857395)
    ·
      refine ⟨144695917420254308122286093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96463944946836205414857395 144695917420254308122286093)
      ·
        refine ⟨54260969032595365545857285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144695917420254308122286093 54260969032595365545857285)
        ·
          refine ⟨10173931693611631039848241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54260969032595365545857285 10173931693611631039848241)
          ·
            refine ⟨7630448770208723279886181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10173931693611631039848241 7630448770208723279886181)
            ·
              refine ⟨1430709144414135614978659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7630448770208723279886181 1430709144414135614978659)
              ·
                refine ⟨2146063716621203422467989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1430709144414135614978659 2146063716621203422467989)
                ·
                  refine ⟨100596736716618910428187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2146063716621203422467989 100596736716618910428187)
                  ·
                    rfl

theorem cell23_1763203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 6].length) (baseStart_1763203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763203 prefixEnd_1763203 := by exact prefixLift 1763203
  have htrace : WordTrace (prefixWord ++ tailWord_1763203) baseStart_1763203 baseEnd_1763203 := by
    simpa [prefixWord, tailWord_1763203, baseEnd_1763203] using wordTrace_append hprefix tailTrace_1763203
  have hstable : (prefixWord ++ tailWord_1763203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763203).length < 2 ^ (prefixWord ++ tailWord_1763203).sum := by decide
  have hdescent : baseEnd_1763203 < baseStart_1763203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763253 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_1763253 : Nat := 118140960795 + 1763253 * 2 ^ 59
def prefixEnd_1763253 : Nat := 4983230072969 + 3 ^ 40 * 1763253 * 2
def baseEnd_1763253 : Nat := 905396304482294998228453

theorem tailTrace_1763253 : CollatzResearch.WordTrace tailWord_1763253 prefixEnd_1763253 905396304482294998228453 := by
  unfold tailWord_1763253
  simp only [CollatzResearch.WordTrace]
  refine ⟨64311120281042995482558413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42874080187361996988372275 64311120281042995482558413)
  ·
    refine ⟨24116670105391123305959405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64311120281042995482558413 24116670105391123305959405)
    ·
      refine ⟨9043751289521671239734777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24116670105391123305959405 9043751289521671239734777)
      ·
        refine ⟨6782813467141253429801083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9043751289521671239734777 6782813467141253429801083)
        ·
          refine ⟨10174220200711880144701625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6782813467141253429801083 10174220200711880144701625)
          ·
            refine ⟨7630665150533910108526219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10174220200711880144701625 7630665150533910108526219)
            ·
              refine ⟨11445997725800865162789329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7630665150533910108526219 11445997725800865162789329)
              ·
                refine ⟨8584498294350648872091997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11445997725800865162789329 8584498294350648872091997)
                ·
                  refine ⟨3219186860381493327034499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8584498294350648872091997 3219186860381493327034499)
                  ·
                    refine ⟨4828780290572239990551749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3219186860381493327034499 4828780290572239990551749)
                    ·
                      refine ⟨905396304482294998228453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4828780290572239990551749 905396304482294998228453)
                      ·
                        rfl

theorem cell23_1763253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_1763253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763253 prefixEnd_1763253 := by exact prefixLift 1763253
  have htrace : WordTrace (prefixWord ++ tailWord_1763253) baseStart_1763253 baseEnd_1763253 := by
    simpa [prefixWord, tailWord_1763253, baseEnd_1763253] using wordTrace_append hprefix tailTrace_1763253
  have hstable : (prefixWord ++ tailWord_1763253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763253).length < 2 ^ (prefixWord ++ tailWord_1763253).sum := by decide
  have hdescent : baseEnd_1763253 < baseStart_1763253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763256 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 3, 1, 5]
def baseStart_1763256 : Nat := 118140960795 + 1763256 * 2 ^ 59
def prefixEnd_1763256 : Nat := 4983230072969 + 3 ^ 40 * 1763256 * 2
def baseEnd_1763256 : Nat := 905397844924258486490939

theorem tailTrace_1763256 : CollatzResearch.WordTrace tailWord_1763256 prefixEnd_1763256 905397844924258486490939 := by
  unfold tailWord_1763256
  simp only [CollatzResearch.WordTrace]
  refine ⟨32155614850016063497458811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42874153133354751329945081 32155614850016063497458811)
  ·
    refine ⟨48233422275024095246188217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32155614850016063497458811 48233422275024095246188217)
    ·
      refine ⟨36175066706268071434641163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48233422275024095246188217 36175066706268071434641163)
      ·
        refine ⟨54262600059402107151961745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36175066706268071434641163 54262600059402107151961745)
        ·
          refine ⟨40696950044551580363971309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54262600059402107151961745 40696950044551580363971309)
          ·
            refine ⟨15261356266706842636489241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40696950044551580363971309 15261356266706842636489241)
            ·
              refine ⟨11446017200030131977366931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15261356266706842636489241 11446017200030131977366931)
              ·
                refine ⟨17169025800045197966050397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11446017200030131977366931 17169025800045197966050397)
                ·
                  refine ⟨6438384675016949237268899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17169025800045197966050397 6438384675016949237268899)
                  ·
                    refine ⟨9657577012525423855903349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6438384675016949237268899 9657577012525423855903349)
                    ·
                      refine ⟨905397844924258486490939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9657577012525423855903349 905397844924258486490939)
                      ·
                        rfl

theorem cell23_1763256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_1763256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763256 prefixEnd_1763256 := by exact prefixLift 1763256
  have htrace : WordTrace (prefixWord ++ tailWord_1763256) baseStart_1763256 baseEnd_1763256 := by
    simpa [prefixWord, tailWord_1763256, baseEnd_1763256] using wordTrace_append hprefix tailTrace_1763256
  have hstable : (prefixWord ++ tailWord_1763256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763256).length < 2 ^ (prefixWord ++ tailWord_1763256).sum := by decide
  have hdescent : baseEnd_1763256 < baseStart_1763256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763263 : List Nat := [1, 1, 2, 2, 2, 1, 3, 5, 2, 4]
def baseStart_1763263 : Nat := 118140960795 + 1763263 * 2 ^ 59
def prefixEnd_1763263 : Nat := 4983230072969 + 3 ^ 40 * 1763263 * 2
def baseEnd_1763263 : Nat := 301800479762946653034469

theorem tailTrace_1763263 : CollatzResearch.WordTrace tailWord_1763263 prefixEnd_1763263 301800479762946653034469 := by
  unfold tailWord_1763263
  simp only [CollatzResearch.WordTrace]
  refine ⟨64311485011006767190422443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42874323340671178126948295 64311485011006767190422443)
  ·
    refine ⟨96467227516510150785633665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64311485011006767190422443 96467227516510150785633665)
    ·
      refine ⟨72350420637382613089225249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96467227516510150785633665 72350420637382613089225249)
      ·
        refine ⟨54262815478036959816918937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72350420637382613089225249 54262815478036959816918937)
        ·
          refine ⟨40697111608527719862689203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54262815478036959816918937 40697111608527719862689203)
          ·
            refine ⟨61045667412791579794033805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40697111608527719862689203 61045667412791579794033805)
            ·
              refine ⟨22892125279796842422762677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61045667412791579794033805 22892125279796842422762677)
              ·
                refine ⟨2146136744980953977134001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22892125279796842422762677 2146136744980953977134001)
                ·
                  refine ⟨1609602558735715482850501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2146136744980953977134001 1609602558735715482850501)
                  ·
                    refine ⟨301800479762946653034469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1609602558735715482850501 301800479762946653034469)
                    ·
                      rfl

theorem cell23_1763263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 4].length) (baseStart_1763263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763263 prefixEnd_1763263 := by exact prefixLift 1763263
  have htrace : WordTrace (prefixWord ++ tailWord_1763263) baseStart_1763263 baseEnd_1763263 := by
    simpa [prefixWord, tailWord_1763263, baseEnd_1763263] using wordTrace_append hprefix tailTrace_1763263
  have hstable : (prefixWord ++ tailWord_1763263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763263).length < 2 ^ (prefixWord ++ tailWord_1763263).sum := by decide
  have hdescent : baseEnd_1763263 < baseStart_1763263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763293 : List Nat := [1, 4, 3, 1, 3, 1, 10]
def baseStart_1763293 : Nat := 118140960795 + 1763293 * 2 ^ 59
def prefixEnd_1763293 : Nat := 4983230072969 + 3 ^ 40 * 1763293 * 2
def baseEnd_1763293 : Nat := 11177985724795985700349

theorem tailTrace_1763293 : CollatzResearch.WordTrace tailWord_1763293 prefixEnd_1763293 11177985724795985700349 := by
  unfold tailWord_1763293
  simp only [CollatzResearch.WordTrace]
  refine ⟨64312579200898082314014533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42875052800598721542676355 64312579200898082314014533)
  ·
    refine ⟨12058608600168390433877725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64312579200898082314014533 12058608600168390433877725)
    ·
      refine ⟨4521978225063146412704147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12058608600168390433877725 4521978225063146412704147)
      ·
        refine ⟨6782967337594719619056221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4521978225063146412704147 6782967337594719619056221)
        ·
          refine ⟨2543612751598019857146083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6782967337594719619056221 2543612751598019857146083)
          ·
            refine ⟨3815419127397029785719125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543612751598019857146083 3815419127397029785719125)
            ·
              refine ⟨11177985724795985700349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3815419127397029785719125 11177985724795985700349)
              ·
                rfl

theorem cell23_1763293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 10].length) (baseStart_1763293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763293 prefixEnd_1763293 := by exact prefixLift 1763293
  have htrace : WordTrace (prefixWord ++ tailWord_1763293) baseStart_1763293 baseEnd_1763293 := by
    simpa [prefixWord, tailWord_1763293, baseEnd_1763293] using wordTrace_append hprefix tailTrace_1763293
  have hstable : (prefixWord ++ tailWord_1763293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763293).length < 2 ^ (prefixWord ++ tailWord_1763293).sum := by decide
  have hdescent : baseEnd_1763293 < baseStart_1763293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763320 : List Nat := [2, 1, 2, 1, 1, 3, 2, 5, 2, 1, 3]
def baseStart_1763320 : Nat := 118140960795 + 1763320 * 2 ^ 59
def prefixEnd_1763320 : Nat := 4983230072969 + 3 ^ 40 * 1763320 * 2
def baseEnd_1763320 : Nat := 905430707686146236090645

theorem tailTrace_1763320 : CollatzResearch.WordTrace tailWord_1763320 prefixEnd_1763320 905430707686146236090645 := by
  unfold tailWord_1763320
  simp only [CollatzResearch.WordTrace]
  refine ⟨32156781985900132962623707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42875709314533510616831609 32156781985900132962623707)
  ·
    refine ⟨48235172978850199443935561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32156781985900132962623707 48235172978850199443935561)
    ·
      refine ⟨36176379734137649582951671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48235172978850199443935561 36176379734137649582951671)
      ·
        refine ⟨54264569601206474374427507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36176379734137649582951671 54264569601206474374427507)
        ·
          refine ⟨81396854401809711561641261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54264569601206474374427507 81396854401809711561641261)
          ·
            refine ⟨30523820400678641835615473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81396854401809711561641261 30523820400678641835615473)
            ·
              refine ⟨22892865300508981376711605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30523820400678641835615473 22892865300508981376711605)
              ·
                refine ⟨2146206121922717004066713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22892865300508981376711605 2146206121922717004066713)
                ·
                  refine ⟨1609654591442037753050035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2146206121922717004066713 1609654591442037753050035)
                  ·
                    refine ⟨2414481887163056629575053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1609654591442037753050035 2414481887163056629575053)
                    ·
                      refine ⟨905430707686146236090645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2414481887163056629575053 905430707686146236090645)
                      ·
                        rfl

theorem cell23_1763320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 2, 1, 3].length) (baseStart_1763320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763320 prefixEnd_1763320 := by exact prefixLift 1763320
  have htrace : WordTrace (prefixWord ++ tailWord_1763320) baseStart_1763320 baseEnd_1763320 := by
    simpa [prefixWord, tailWord_1763320, baseEnd_1763320] using wordTrace_append hprefix tailTrace_1763320
  have hstable : (prefixWord ++ tailWord_1763320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763320).length < 2 ^ (prefixWord ++ tailWord_1763320).sum := by decide
  have hdescent : baseEnd_1763320 < baseStart_1763320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763338 : List Nat := [3, 1, 2, 2, 5, 1, 1, 3, 1, 2, 2]
def baseStart_1763338 : Nat := 118140960795 + 1763338 * 2 ^ 59
def prefixEnd_1763338 : Nat := 4983230072969 + 3 ^ 40 * 1763338 * 2
def baseEnd_1763338 : Nat := 905439950337927165665563

theorem tailTrace_1763338 : CollatzResearch.WordTrace tailWord_1763338 prefixEnd_1763338 905439950337927165665563 := by
  unfold tailWord_1763338
  simp only [CollatzResearch.WordTrace]
  refine ⟨16078555121433763749850667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42876146990490036666268445 16078555121433763749850667)
  ·
    refine ⟨24117832682150645624776001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16078555121433763749850667 24117832682150645624776001)
    ·
      refine ⟨18088374511612984218582001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24117832682150645624776001 18088374511612984218582001)
      ·
        refine ⟨13566280883709738163936501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18088374511612984218582001 13566280883709738163936501)
        ·
          refine ⟨1271838832847787952869047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13566280883709738163936501 1271838832847787952869047)
          ·
            refine ⟨1907758249271681929303571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271838832847787952869047 1907758249271681929303571)
            ·
              refine ⟨2861637373907522893955357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1907758249271681929303571 2861637373907522893955357)
              ·
                refine ⟨1073114015215321085233259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2861637373907522893955357 1073114015215321085233259)
                ·
                  refine ⟨1609671022822981627849889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1073114015215321085233259 1609671022822981627849889)
                  ·
                    refine ⟨1207253267117236220887417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1609671022822981627849889 1207253267117236220887417)
                    ·
                      refine ⟨905439950337927165665563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1207253267117236220887417 905439950337927165665563)
                      ·
                        rfl

theorem cell23_1763338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_1763338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763338 prefixEnd_1763338 := by exact prefixLift 1763338
  have htrace : WordTrace (prefixWord ++ tailWord_1763338) baseStart_1763338 baseEnd_1763338 := by
    simpa [prefixWord, tailWord_1763338, baseEnd_1763338] using wordTrace_append hprefix tailTrace_1763338
  have hstable : (prefixWord ++ tailWord_1763338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763338).length < 2 ^ (prefixWord ++ tailWord_1763338).sum := by decide
  have hdescent : baseEnd_1763338 < baseStart_1763338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763363 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 3]
def baseStart_1763363 : Nat := 118140960795 + 1763363 * 2 ^ 59
def prefixEnd_1763363 : Nat := 4983230072969 + 3 ^ 40 * 1763363 * 2
def baseEnd_1763363 : Nat := 905452787354289567852947

theorem tailTrace_1763363 : CollatzResearch.WordTrace tailWord_1763363 prefixEnd_1763363 905452787354289567852947 := by
  unfold tailWord_1763363
  simp only [CollatzResearch.WordTrace]
  refine ⟨64315132310644484269062743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42876754873762989512708495 64315132310644484269062743)
  ·
    refine ⟨96472698465966726403594115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64315132310644484269062743 96472698465966726403594115)
    ·
      refine ⟨144709047698950089605391173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96472698465966726403594115 144709047698950089605391173)
      ·
        refine ⟨27132946443553141801010845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144709047698950089605391173 27132946443553141801010845)
        ·
          refine ⟨10174854916332428175379067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27132946443553141801010845 10174854916332428175379067)
          ·
            refine ⟨15262282374498642263068601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10174854916332428175379067 15262282374498642263068601)
            ·
              refine ⟨11446711780873981697301451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15262282374498642263068601 11446711780873981697301451)
              ·
                refine ⟨17170067671310972545952177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11446711780873981697301451 17170067671310972545952177)
                ·
                  refine ⟨12877550753483229409464133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17170067671310972545952177 12877550753483229409464133)
                  ·
                    refine ⟨2414540766278105514274525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12877550753483229409464133 2414540766278105514274525)
                    ·
                      refine ⟨905452787354289567852947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2414540766278105514274525 905452787354289567852947)
                      ·
                        rfl

theorem cell23_1763363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_1763363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763363 prefixEnd_1763363 := by exact prefixLift 1763363
  have htrace : WordTrace (prefixWord ++ tailWord_1763363) baseStart_1763363 baseEnd_1763363 := by
    simpa [prefixWord, tailWord_1763363, baseEnd_1763363] using wordTrace_append hprefix tailTrace_1763363
  have hstable : (prefixWord ++ tailWord_1763363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763363).length < 2 ^ (prefixWord ++ tailWord_1763363).sum := by decide
  have hdescent : baseEnd_1763363 < baseStart_1763363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763433 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 1, 3, 4]
def baseStart_1763433 : Nat := 118140960795 + 1763433 * 2 ^ 59
def prefixEnd_1763433 : Nat := 4983230072969 + 3 ^ 40 * 1763433 * 2
def baseEnd_1763433 : Nat := 905488731000104293977625

theorem tailTrace_1763433 : CollatzResearch.WordTrace tailWord_1763433 prefixEnd_1763433 905488731000104293977625 := by
  unfold tailWord_1763433
  simp only [CollatzResearch.WordTrace]
  refine ⟨64317685420390886224110953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42878456946927257482740635 64317685420390886224110953)
  ·
    refine ⟨48238264065293164668083215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64317685420390886224110953 48238264065293164668083215)
    ·
      refine ⟨72357396097939747002124823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48238264065293164668083215 72357396097939747002124823)
      ·
        refine ⟨108536094146909620503187235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72357396097939747002124823 108536094146909620503187235)
        ·
          refine ⟨162804141220364430754780853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108536094146909620503187235 162804141220364430754780853)
          ·
            refine ⟨15262888239409165383260705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162804141220364430754780853 15262888239409165383260705)
            ·
              refine ⟨11447166179556874037445529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15262888239409165383260705 11447166179556874037445529)
              ·
                refine ⟨8585374634667655528084147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11447166179556874037445529 8585374634667655528084147)
                ·
                  refine ⟨12878061952001483292126221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8585374634667655528084147 12878061952001483292126221)
                  ·
                    refine ⟨4829273232000556234547333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12878061952001483292126221 4829273232000556234547333)
                    ·
                      refine ⟨905488731000104293977625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4829273232000556234547333 905488731000104293977625)
                      ·
                        rfl

theorem cell23_1763433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 3, 4].length) (baseStart_1763433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763433 prefixEnd_1763433 := by exact prefixLift 1763433
  have htrace : WordTrace (prefixWord ++ tailWord_1763433) baseStart_1763433 baseEnd_1763433 := by
    simpa [prefixWord, tailWord_1763433, baseEnd_1763433] using wordTrace_append hprefix tailTrace_1763433
  have hstable : (prefixWord ++ tailWord_1763433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763433).length < 2 ^ (prefixWord ++ tailWord_1763433).sum := by decide
  have hdescent : baseEnd_1763433 < baseStart_1763433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763460 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 5, 4]
def baseStart_1763460 : Nat := 118140960795 + 1763460 * 2 ^ 59
def prefixEnd_1763460 : Nat := 4983230072969 + 3 ^ 40 * 1763460 * 2
def baseEnd_1763460 : Nat := 301834198325925229446667

theorem tailTrace_1763460 : CollatzResearch.WordTrace tailWord_1763460 prefixEnd_1763460 301834198325925229446667 := by
  unfold tailWord_1763460
  simp only [CollatzResearch.WordTrace]
  refine ⟨32159335095646534917671917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42879113460862046556895889 32159335095646534917671917)
  ·
    refine ⟨12059750660867450594126969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32159335095646534917671917 12059750660867450594126969)
    ·
      refine ⟨9044812995650587945595227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12059750660867450594126969 9044812995650587945595227)
      ·
        refine ⟨13567219493475881918392841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9044812995650587945595227 13567219493475881918392841)
        ·
          refine ⟨10175414620106911438794631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13567219493475881918392841 10175414620106911438794631)
          ·
            refine ⟨15263121930160367158191947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10175414620106911438794631 15263121930160367158191947)
            ·
              refine ⟨22894682895240550737287921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15263121930160367158191947 22894682895240550737287921)
              ·
                refine ⟨17171012171430413052965941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22894682895240550737287921 17171012171430413052965941)
                ·
                  refine ⟨1609782391071601223715557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17171012171430413052965941 1609782391071601223715557)
                  ·
                    refine ⟨301834198325925229446667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1609782391071601223715557 301834198325925229446667)
                    ·
                      rfl

theorem cell23_1763460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_1763460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763460 prefixEnd_1763460 := by exact prefixLift 1763460
  have htrace : WordTrace (prefixWord ++ tailWord_1763460) baseStart_1763460 baseEnd_1763460 := by
    simpa [prefixWord, tailWord_1763460, baseEnd_1763460] using wordTrace_append hprefix tailTrace_1763460
  have hstable : (prefixWord ++ tailWord_1763460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763460).length < 2 ^ (prefixWord ++ tailWord_1763460).sum := by decide
  have hdescent : baseEnd_1763460 < baseStart_1763460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763463 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_1763463 : Nat := 118140960795 + 1763463 * 2 ^ 59
def prefixEnd_1763463 : Nat := 4983230072969 + 3 ^ 40 * 1763463 * 2
def baseEnd_1763463 : Nat := 905504135419739176602487

theorem tailTrace_1763463 : CollatzResearch.WordTrace tailWord_1763463 prefixEnd_1763463 905504135419739176602487 := by
  unfold tailWord_1763463
  simp only [CollatzResearch.WordTrace]
  refine ⟨64318779610282201347703043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42879186406854800898468695 64318779610282201347703043)
  ·
    refine ⟨96478169415423302021554565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64318779610282201347703043 96478169415423302021554565)
    ·
      refine ⟨18089656765391869129041481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96478169415423302021554565 18089656765391869129041481)
      ·
        refine ⟨13567242574043901846781111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18089656765391869129041481 13567242574043901846781111)
        ·
          refine ⟨20350863861065852770171667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13567242574043901846781111 20350863861065852770171667)
          ·
            refine ⟨30526295791598779155257501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20350863861065852770171667 30526295791598779155257501)
            ·
              refine ⟨11447360921849542183221563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30526295791598779155257501 11447360921849542183221563)
              ·
                refine ⟨17171041382774313274832345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11447360921849542183221563 17171041382774313274832345)
                ·
                  refine ⟨12878281037080734956124259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17171041382774313274832345 12878281037080734956124259)
                  ·
                    refine ⟨19317421555621102434186389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12878281037080734956124259 19317421555621102434186389)
                    ·
                      refine ⟨905504135419739176602487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19317421555621102434186389 905504135419739176602487)
                      ·
                        rfl

theorem cell23_1763463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_1763463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763463 prefixEnd_1763463 := by exact prefixLift 1763463
  have htrace : WordTrace (prefixWord ++ tailWord_1763463) baseStart_1763463 baseEnd_1763463 := by
    simpa [prefixWord, tailWord_1763463, baseEnd_1763463] using wordTrace_append hprefix tailTrace_1763463
  have hstable : (prefixWord ++ tailWord_1763463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763463).length < 2 ^ (prefixWord ++ tailWord_1763463).sum := by decide
  have hdescent : baseEnd_1763463 < baseStart_1763463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763477 : List Nat := [1, 3, 2, 1, 1, 1, 3, 6, 1, 4]
def baseStart_1763477 : Nat := 118140960795 + 1763477 * 2 ^ 59
def prefixEnd_1763477 : Nat := 4983230072969 + 3 ^ 40 * 1763477 * 2
def baseEnd_1763477 : Nat := 301837108049634040609141

theorem tailTrace_1763477 : CollatzResearch.WordTrace tailWord_1763477 prefixEnd_1763477 301837108049634040609141 := by
  unfold tailWord_1763477
  simp only [CollatzResearch.WordTrace]
  refine ⟨64319290232231481738712685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42879526821487654492475123 64319290232231481738712685)
  ·
    refine ⟨24119733837086805652017257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64319290232231481738712685 24119733837086805652017257)
    ·
      refine ⟨18089800377815104239012943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24119733837086805652017257 18089800377815104239012943)
      ·
        refine ⟨27134700566722656358519415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18089800377815104239012943 27134700566722656358519415)
        ·
          refine ⟨40702050850083984537779123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27134700566722656358519415 40702050850083984537779123)
          ·
            refine ⟨61053076275125976806668685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40702050850083984537779123 61053076275125976806668685)
            ·
              refine ⟨22894903603172241302500757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61053076275125976806668685 22894903603172241302500757)
              ·
                refine ⟨1073198606398698811054723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22894903603172241302500757 1073198606398698811054723)
                ·
                  refine ⟨1609797909598048216582085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1073198606398698811054723 1609797909598048216582085)
                  ·
                    refine ⟨301837108049634040609141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1609797909598048216582085 301837108049634040609141)
                    ·
                      rfl

theorem cell23_1763477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_1763477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763477 prefixEnd_1763477 := by exact prefixLift 1763477
  have htrace : WordTrace (prefixWord ++ tailWord_1763477) baseStart_1763477 baseEnd_1763477 := by
    simpa [prefixWord, tailWord_1763477, baseEnd_1763477] using wordTrace_append hprefix tailTrace_1763477
  have hstable : (prefixWord ++ tailWord_1763477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763477).length < 2 ^ (prefixWord ++ tailWord_1763477).sum := by decide
  have hdescent : baseEnd_1763477 < baseStart_1763477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763493 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 1, 2, 6]
def baseStart_1763493 : Nat := 118140960795 + 1763493 * 2 ^ 59
def prefixEnd_1763493 : Nat := 4983230072969 + 3 ^ 40 * 1763493 * 2
def baseEnd_1763493 : Nat := 905519539839374059227349

theorem tailTrace_1763493 : CollatzResearch.WordTrace tailWord_1763493 prefixEnd_1763493 905519539839374059227349 := by
  unfold tailWord_1763493
  simp only [CollatzResearch.WordTrace]
  refine ⟨64319873800173516471295133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42879915866782344314196755 64319873800173516471295133)
  ·
    refine ⟨24119952675065068676735675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64319873800173516471295133 24119952675065068676735675)
    ·
      refine ⟨36179929012597603015103513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24119952675065068676735675 36179929012597603015103513)
      ·
        refine ⟨27134946759448202261327635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36179929012597603015103513 27134946759448202261327635)
        ·
          refine ⟨40702420139172303391991453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27134946759448202261327635 40702420139172303391991453)
          ·
            refine ⟨15263407552189613771996795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40702420139172303391991453 15263407552189613771996795)
            ·
              refine ⟨22895111328284420657995193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15263407552189613771996795 22895111328284420657995193)
              ·
                refine ⟨17171333496213315493496395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22895111328284420657995193 17171333496213315493496395)
                ·
                  refine ⟨25757000244319973240244593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17171333496213315493496395 25757000244319973240244593)
                  ·
                    refine ⟨19317750183239979930183445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25757000244319973240244593 19317750183239979930183445)
                    ·
                      refine ⟨905519539839374059227349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19317750183239979930183445 905519539839374059227349)
                      ·
                        rfl

theorem cell23_1763493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_1763493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763493 prefixEnd_1763493 := by exact prefixLift 1763493
  have htrace : WordTrace (prefixWord ++ tailWord_1763493) baseStart_1763493 baseEnd_1763493 := by
    simpa [prefixWord, tailWord_1763493, baseEnd_1763493] using wordTrace_append hprefix tailTrace_1763493
  have hstable : (prefixWord ++ tailWord_1763493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763493).length < 2 ^ (prefixWord ++ tailWord_1763493).sum := by decide
  have hdescent : baseEnd_1763493 < baseStart_1763493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763523 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 4]
def baseStart_1763523 : Nat := 118140960795 + 1763523 * 2 ^ 59
def prefixEnd_1763523 : Nat := 4983230072969 + 3 ^ 40 * 1763523 * 2
def baseEnd_1763523 : Nat := 905534944259008941852211

theorem tailTrace_1763523 : CollatzResearch.WordTrace tailWord_1763523 prefixEnd_1763523 905534944259008941852211 := by
  unfold tailWord_1763523
  simp only [CollatzResearch.WordTrace]
  refine ⟨64320967990064831594887223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42880645326709887729924815 64320967990064831594887223)
  ·
    refine ⟨96481451985097247392330835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64320967990064831594887223 96481451985097247392330835)
    ·
      refine ⟨144722177977645871088496253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96481451985097247392330835 144722177977645871088496253)
      ·
        refine ⟨54270816741617201658186095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144722177977645871088496253 54270816741617201658186095)
        ·
          refine ⟨81406225112425802487279143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54270816741617201658186095 81406225112425802487279143)
          ·
            refine ⟨122109337668638703730918715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81406225112425802487279143 122109337668638703730918715)
            ·
              refine ⟨183164006502958055596378073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122109337668638703730918715 183164006502958055596378073)
              ·
                refine ⟨137373004877218541697283555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183164006502958055596378073 137373004877218541697283555)
                ·
                  refine ⟨206059507315827812545925333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137373004877218541697283555 206059507315827812545925333)
                  ·
                    refine ⟨4829519702714714356545125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 206059507315827812545925333 4829519702714714356545125)
                    ·
                      refine ⟨905534944259008941852211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4829519702714714356545125 905534944259008941852211)
                      ·
                        rfl

theorem cell23_1763523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_1763523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763523 prefixEnd_1763523 := by exact prefixLift 1763523
  have htrace : WordTrace (prefixWord ++ tailWord_1763523) baseStart_1763523 baseEnd_1763523 := by
    simpa [prefixWord, tailWord_1763523, baseEnd_1763523] using wordTrace_append hprefix tailTrace_1763523
  have hstable : (prefixWord ++ tailWord_1763523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763523).length < 2 ^ (prefixWord ++ tailWord_1763523).sum := by decide
  have hdescent : baseEnd_1763523 < baseStart_1763523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763534 : List Nat := [4, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3]
def baseStart_1763534 : Nat := 118140960795 + 1763534 * 2 ^ 59
def prefixEnd_1763534 : Nat := 4983230072969 + 3 ^ 40 * 1763534 * 2
def baseEnd_1763534 : Nat := 905540592546208398814661

theorem tailTrace_1763534 : CollatzResearch.WordTrace tailWord_1763534 prefixEnd_1763534 905540592546208398814661 := by
  unfold tailWord_1763534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8040171149128122559192207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42880912795349986982358437 8040171149128122559192207)
  ·
    refine ⟨12060256723692183838788311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8040171149128122559192207 12060256723692183838788311)
    ·
      refine ⟨18090385085538275758182467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12060256723692183838788311 18090385085538275758182467)
      ·
        refine ⟨27135577628307413637273701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18090385085538275758182467 27135577628307413637273701)
        ·
          refine ⟨5087920805307640056988819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27135577628307413637273701 5087920805307640056988819)
          ·
            refine ⟨7631881207961460085483229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5087920805307640056988819 7631881207961460085483229)
            ·
              refine ⟨2861955452985547532056211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7631881207961460085483229 2861955452985547532056211)
              ·
                refine ⟨4292933179478321298084317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2861955452985547532056211 4292933179478321298084317)
                ·
                  refine ⟨1609849942304370486781619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4292933179478321298084317 1609849942304370486781619)
                  ·
                    refine ⟨2414774913456555730172429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1609849942304370486781619 2414774913456555730172429)
                    ·
                      refine ⟨905540592546208398814661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2414774913456555730172429 905540592546208398814661)
                      ·
                        rfl

theorem cell23_1763534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_1763534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763534 prefixEnd_1763534 := by exact prefixLift 1763534
  have htrace : WordTrace (prefixWord ++ tailWord_1763534) baseStart_1763534 baseEnd_1763534 := by
    simpa [prefixWord, tailWord_1763534, baseEnd_1763534] using wordTrace_append hprefix tailTrace_1763534
  have hstable : (prefixWord ++ tailWord_1763534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763534).length < 2 ^ (prefixWord ++ tailWord_1763534).sum := by decide
  have hdescent : baseEnd_1763534 < baseStart_1763534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763541 : List Nat := [1, 3, 2, 4, 3, 1, 2, 1, 6]
def baseStart_1763541 : Nat := 118140960795 + 1763541 * 2 ^ 59
def prefixEnd_1763541 : Nat := 4983230072969 + 3 ^ 40 * 1763541 * 2
def baseEnd_1763541 : Nat := 100616020767865541269681

theorem tailTrace_1763541 : CollatzResearch.WordTrace tailWord_1763541 prefixEnd_1763541 100616020767865541269681 := by
  unfold tailWord_1763541
  simp only [CollatzResearch.WordTrace]
  refine ⟨64321624503999620669042477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42881083002666413779361651 64321624503999620669042477)
  ·
    refine ⟨24120609188999857750890929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64321624503999620669042477 24120609188999857750890929)
    ·
      refine ⟨18090456891749893313168197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24120609188999857750890929 18090456891749893313168197)
      ·
        refine ⟨3391960667203104996219037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18090456891749893313168197 3391960667203104996219037)
        ·
          refine ⟨1271985250201164373582139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3391960667203104996219037 1271985250201164373582139)
          ·
            refine ⟨1907977875301746560373209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271985250201164373582139 1907977875301746560373209)
            ·
              refine ⟨1430983406476309920279907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1907977875301746560373209 1430983406476309920279907)
              ·
                refine ⟨2146475109714464880419861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1430983406476309920279907 2146475109714464880419861)
                ·
                  refine ⟨100616020767865541269681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2146475109714464880419861 100616020767865541269681)
                  ·
                    rfl

theorem cell23_1763541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 6].length) (baseStart_1763541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763541 prefixEnd_1763541 := by exact prefixLift 1763541
  have htrace : WordTrace (prefixWord ++ tailWord_1763541) baseStart_1763541 baseEnd_1763541 := by
    simpa [prefixWord, tailWord_1763541, baseEnd_1763541] using wordTrace_append hprefix tailTrace_1763541
  have hstable : (prefixWord ++ tailWord_1763541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763541).length < 2 ^ (prefixWord ++ tailWord_1763541).sum := by decide
  have hdescent : baseEnd_1763541 < baseStart_1763541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763557 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 3, 1, 4]
def baseStart_1763557 : Nat := 118140960795 + 1763557 * 2 ^ 59
def prefixEnd_1763557 : Nat := 4983230072969 + 3 ^ 40 * 1763557 * 2
def baseEnd_1763557 : Nat := 905552402601261808827055

theorem tailTrace_1763557 : CollatzResearch.WordTrace tailWord_1763557 prefixEnd_1763557 905552402601261808827055 := by
  unfold tailWord_1763557
  simp only [CollatzResearch.WordTrace]
  refine ⟨64322208071941655401624925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42881472047961103601083283 64322208071941655401624925)
  ·
    refine ⟨24120828026978120775609347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64322208071941655401624925 24120828026978120775609347)
    ·
      refine ⟨36181242040467181163414021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24120828026978120775609347 36181242040467181163414021)
      ·
        refine ⟨6783982882587596468140129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36181242040467181163414021 6783982882587596468140129)
        ·
          refine ⟨5087987161940697351105097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6783982882587596468140129 5087987161940697351105097)
          ·
            refine ⟨3815990371455523013328823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5087987161940697351105097 3815990371455523013328823)
            ·
              refine ⟨5723985557183284519993235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3815990371455523013328823 5723985557183284519993235)
              ·
                refine ⟨8585978335774926779989853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5723985557183284519993235 8585978335774926779989853)
                ·
                  refine ⟨3219741875915597542496195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8585978335774926779989853 3219741875915597542496195)
                  ·
                    refine ⟨4829612813873396313744293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3219741875915597542496195 4829612813873396313744293)
                    ·
                      refine ⟨905552402601261808827055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4829612813873396313744293 905552402601261808827055)
                      ·
                        rfl

theorem cell23_1763557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_1763557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763557 prefixEnd_1763557 := by exact prefixLift 1763557
  have htrace : WordTrace (prefixWord ++ tailWord_1763557) baseStart_1763557 baseEnd_1763557 := by
    simpa [prefixWord, tailWord_1763557, baseEnd_1763557] using wordTrace_append hprefix tailTrace_1763557
  have hstable : (prefixWord ++ tailWord_1763557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763557).length < 2 ^ (prefixWord ++ tailWord_1763557).sum := by decide
  have hdescent : baseEnd_1763557 < baseStart_1763557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763563 : List Nat := [1, 1, 1, 1, 2, 5, 1, 11]
def baseStart_1763563 : Nat := 118140960795 + 1763563 * 2 ^ 59
def prefixEnd_1763563 : Nat := 4983230072969 + 3 ^ 40 * 1763563 * 2
def baseEnd_1763563 : Nat := 33539091980932917976001

theorem tailTrace_1763563 : CollatzResearch.WordTrace tailWord_1763563 prefixEnd_1763563 33539091980932917976001 := by
  unfold tailWord_1763563
  simp only [CollatzResearch.WordTrace]
  refine ⟨64322426909919918426343343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42881617939946612284228895 64322426909919918426343343)
  ·
    refine ⟨96483640364879877639515015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64322426909919918426343343 96483640364879877639515015)
    ·
      refine ⟨144725460547319816459272523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96483640364879877639515015 144725460547319816459272523)
      ·
        refine ⟨217088190820979724688908785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144725460547319816459272523 217088190820979724688908785)
        ·
          refine ⟨162816143115734793516681589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217088190820979724688908785 162816143115734793516681589)
          ·
            refine ⟨15264013417100136892188899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162816143115734793516681589 15264013417100136892188899)
            ·
              refine ⟨22896020125650205338283349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15264013417100136892188899 22896020125650205338283349)
              ·
                refine ⟨33539091980932917976001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 22896020125650205338283349 33539091980932917976001)
                ·
                  rfl

theorem cell23_1763563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 11].length) (baseStart_1763563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763563 prefixEnd_1763563 := by exact prefixLift 1763563
  have htrace : WordTrace (prefixWord ++ tailWord_1763563) baseStart_1763563 baseEnd_1763563 := by
    simpa [prefixWord, tailWord_1763563, baseEnd_1763563] using wordTrace_append hprefix tailTrace_1763563
  have hstable : (prefixWord ++ tailWord_1763563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763563).length < 2 ^ (prefixWord ++ tailWord_1763563).sum := by decide
  have hdescent : baseEnd_1763563 < baseStart_1763563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763607 : List Nat := [1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 3]
def baseStart_1763607 : Nat := 118140960795 + 1763607 * 2 ^ 59
def prefixEnd_1763607 : Nat := 4983230072969 + 3 ^ 40 * 1763607 * 2
def baseEnd_1763607 : Nat := 905578076633986613201825

theorem tailTrace_1763607 : CollatzResearch.WordTrace tailWord_1763607 prefixEnd_1763607 905578076633986613201825 := by
  unfold tailWord_1763607
  simp only [CollatzResearch.WordTrace]
  refine ⟨64324031721760513940945075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42882687814507009293963383 64324031721760513940945075)
  ·
    refine ⟨96486047582640770911417613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64324031721760513940945075 96486047582640770911417613)
    ·
      refine ⟨36182267843490289091781605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96486047582640770911417613 36182267843490289091781605)
      ·
        refine ⟨6784175220654429204709051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36182267843490289091781605 6784175220654429204709051)
        ·
          refine ⟨10176262830981643807063577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6784175220654429204709051 10176262830981643807063577)
          ·
            refine ⟨7632197123236232855297683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10176262830981643807063577 7632197123236232855297683)
            ·
              refine ⟨11448295684854349282946525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7632197123236232855297683 11448295684854349282946525)
              ·
                refine ⟨4293110881820380981104947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11448295684854349282946525 4293110881820380981104947)
                ·
                  refine ⟨6439666322730571471657421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4293110881820380981104947 6439666322730571471657421)
                  ·
                    refine ⟨2414874871023964301871533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6439666322730571471657421 2414874871023964301871533)
                    ·
                      refine ⟨905578076633986613201825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2414874871023964301871533 905578076633986613201825)
                      ·
                        rfl

theorem cell23_1763607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_1763607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763607 prefixEnd_1763607 := by exact prefixLift 1763607
  have htrace : WordTrace (prefixWord ++ tailWord_1763607) baseStart_1763607 baseEnd_1763607 := by
    simpa [prefixWord, tailWord_1763607, baseEnd_1763607] using wordTrace_append hprefix tailTrace_1763607
  have hstable : (prefixWord ++ tailWord_1763607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763607).length < 2 ^ (prefixWord ++ tailWord_1763607).sum := by decide
  have hdescent : baseEnd_1763607 < baseStart_1763607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763640 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 2, 6]
def baseStart_1763640 : Nat := 118140960795 + 1763640 * 2 ^ 59
def prefixEnd_1763640 : Nat := 4983230072969 + 3 ^ 40 * 1763640 * 2
def baseEnd_1763640 : Nat := 301865007165194994696391

theorem tailTrace_1763640 : CollatzResearch.WordTrace tailWord_1763640 prefixEnd_1763640 301865007165194994696391 := by
  unfold tailWord_1763640
  simp only [CollatzResearch.WordTrace]
  refine ⟨32162617665320480288448187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42883490220427307051264249 32162617665320480288448187)
  ·
    refine ⟨48243926497980720432672281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32162617665320480288448187 48243926497980720432672281)
    ·
      refine ⟨36182944873485540324504211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48243926497980720432672281 36182944873485540324504211)
      ·
        refine ⟨54274417310228310486756317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36182944873485540324504211 54274417310228310486756317)
        ·
          refine ⟨20352906491335616432533619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54274417310228310486756317 20352906491335616432533619)
          ·
            refine ⟨30529359737003424648800429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20352906491335616432533619 30529359737003424648800429)
            ·
              refine ⟨11448509901376284243300161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30529359737003424648800429 11448509901376284243300161)
              ·
                refine ⟨8586382426032213182475121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11448509901376284243300161 8586382426032213182475121)
                ·
                  refine ⟨6439786819524159886856341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8586382426032213182475121 6439786819524159886856341)
                  ·
                    refine ⟨301865007165194994696391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6439786819524159886856341 301865007165194994696391)
                    ·
                      rfl

theorem cell23_1763640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_1763640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763640 prefixEnd_1763640 := by exact prefixLift 1763640
  have htrace : WordTrace (prefixWord ++ tailWord_1763640) baseStart_1763640 baseEnd_1763640 := by
    simpa [prefixWord, tailWord_1763640, baseEnd_1763640] using wordTrace_append hprefix tailTrace_1763640
  have hstable : (prefixWord ++ tailWord_1763640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763640).length < 2 ^ (prefixWord ++ tailWord_1763640).sum := by decide
  have hdescent : baseEnd_1763640 < baseStart_1763640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763641 : List Nat := [1, 2, 1, 6, 1, 1, 3, 2, 2, 1, 3]
def baseStart_1763641 : Nat := 118140960795 + 1763641 * 2 ^ 59
def prefixEnd_1763641 : Nat := 4983230072969 + 3 ^ 40 * 1763641 * 2
def baseEnd_1763641 : Nat := 905595534976239480176669

theorem tailTrace_1763641 : CollatzResearch.WordTrace tailWord_1763641 prefixEnd_1763641 905595534976239480176669 := by
  unfold tailWord_1763641
  simp only [CollatzResearch.WordTrace]
  refine ⟨64325271803637337747682777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42883514535758225165121851 64325271803637337747682777)
  ·
    refine ⟨48243953852728003310762083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64325271803637337747682777 48243953852728003310762083)
    ·
      refine ⟨72365930779092004966143125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48243953852728003310762083 72365930779092004966143125)
      ·
        refine ⟨3392153005269937732787959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72365930779092004966143125 3392153005269937732787959)
        ·
          refine ⟨5088229507904906599181939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3392153005269937732787959 5088229507904906599181939)
          ·
            refine ⟨7632344261857359898772909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5088229507904906599181939 7632344261857359898772909)
            ·
              refine ⟨2862129098196509962039841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7632344261857359898772909 2862129098196509962039841)
              ·
                refine ⟨2146596823647382471529881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2862129098196509962039841 2146596823647382471529881)
                ·
                  refine ⟨1609947617735536853647411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2146596823647382471529881 1609947617735536853647411)
                  ·
                    refine ⟨2414921426603305280471117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1609947617735536853647411 2414921426603305280471117)
                    ·
                      refine ⟨905595534976239480176669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2414921426603305280471117 905595534976239480176669)
                      ·
                        rfl

theorem cell23_1763641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_1763641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763641 prefixEnd_1763641 := by exact prefixLift 1763641
  have htrace : WordTrace (prefixWord ++ tailWord_1763641) baseStart_1763641 baseEnd_1763641 := by
    simpa [prefixWord, tailWord_1763641, baseEnd_1763641] using wordTrace_append hprefix tailTrace_1763641
  have hstable : (prefixWord ++ tailWord_1763641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763641).length < 2 ^ (prefixWord ++ tailWord_1763641).sum := by decide
  have hdescent : baseEnd_1763641 < baseStart_1763641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763664 : List Nat := [2, 1, 1, 1, 1, 6, 3, 1, 1, 4, 2]
def baseStart_1763664 : Nat := 118140960795 + 1763664 * 2 ^ 59
def prefixEnd_1763664 : Nat := 4983230072969 + 3 ^ 40 * 1763664 * 2
def baseEnd_1763664 : Nat := 905607345031292890189063

theorem tailTrace_1763664 : CollatzResearch.WordTrace tailWord_1763664 prefixEnd_1763664 905607345031292890189063 := by
  unfold tailWord_1763664
  simp only [CollatzResearch.WordTrace]
  refine ⟨32163055341277006337885023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42884073788369341783846697 32163055341277006337885023)
  ·
    refine ⟨48244583011915509506827535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32163055341277006337885023 48244583011915509506827535)
    ·
      refine ⟨72366874517873264260241303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48244583011915509506827535 72366874517873264260241303)
      ·
        refine ⟨108550311776809896390361955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72366874517873264260241303 108550311776809896390361955)
        ·
          refine ⟨162825467665214844585542933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108550311776809896390361955 162825467665214844585542933)
          ·
            refine ⟨7632443796806945839947325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 162825467665214844585542933 7632443796806945839947325)
            ·
              refine ⟨2862166423802604689980247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7632443796806945839947325 2862166423802604689980247)
              ·
                refine ⟨4293249635703907034970371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2862166423802604689980247 4293249635703907034970371)
                ·
                  refine ⟨6439874453555860552455557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4293249635703907034970371 6439874453555860552455557)
                  ·
                    refine ⟨1207476460041723853585417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6439874453555860552455557 1207476460041723853585417)
                    ·
                      refine ⟨905607345031292890189063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1207476460041723853585417 905607345031292890189063)
                      ·
                        rfl

theorem cell23_1763664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 1, 4, 2].length) (baseStart_1763664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763664 prefixEnd_1763664 := by exact prefixLift 1763664
  have htrace : WordTrace (prefixWord ++ tailWord_1763664) baseStart_1763664 baseEnd_1763664 := by
    simpa [prefixWord, tailWord_1763664, baseEnd_1763664] using wordTrace_append hprefix tailTrace_1763664
  have hstable : (prefixWord ++ tailWord_1763664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763664).length < 2 ^ (prefixWord ++ tailWord_1763664).sum := by decide
  have hdescent : baseEnd_1763664 < baseStart_1763664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763715 : List Nat := [1, 1, 1, 3, 6, 2, 2, 1, 2, 2, 2]
def baseStart_1763715 : Nat := 118140960795 + 1763715 * 2 ^ 59
def prefixEnd_1763715 : Nat := 4983230072969 + 3 ^ 40 * 1763715 * 2
def baseEnd_1763715 : Nat := 905633532544672190651329

theorem tailTrace_1763715 : CollatzResearch.WordTrace tailWord_1763715 prefixEnd_1763715 905633532544672190651329 := by
  unfold tailWord_1763715
  simp only [CollatzResearch.WordTrace]
  refine ⟨64327970805369248385876599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42885313870246165590584399 64327970805369248385876599)
  ·
    refine ⟨96491956208053872578814899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64327970805369248385876599 96491956208053872578814899)
    ·
      refine ⟨144737934312080808868222349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96491956208053872578814899 144737934312080808868222349)
      ·
        refine ⟨54276725367030303325583381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144737934312080808868222349 54276725367030303325583381)
        ·
          refine ⟨2544221501579545468386721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54276725367030303325583381 2544221501579545468386721)
          ·
            refine ⟨1908166126184659101290041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2544221501579545468386721 1908166126184659101290041)
            ·
              refine ⟨1431124594638494325967531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1908166126184659101290041 1431124594638494325967531)
              ·
                refine ⟨2146686891957741488951297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1431124594638494325967531 2146686891957741488951297)
                ·
                  refine ⟨1610015168968306116713473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2146686891957741488951297 1610015168968306116713473)
                  ·
                    refine ⟨1207511376726229587535105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1610015168968306116713473 1207511376726229587535105)
                    ·
                      refine ⟨905633532544672190651329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1207511376726229587535105 905633532544672190651329)
                      ·
                        rfl

theorem cell23_1763715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 2, 2, 2].length) (baseStart_1763715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763715 prefixEnd_1763715 := by exact prefixLift 1763715
  have htrace : WordTrace (prefixWord ++ tailWord_1763715) baseStart_1763715 baseEnd_1763715 := by
    simpa [prefixWord, tailWord_1763715, baseEnd_1763715] using wordTrace_append hprefix tailTrace_1763715
  have hstable : (prefixWord ++ tailWord_1763715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763715).length < 2 ^ (prefixWord ++ tailWord_1763715).sum := by decide
  have hdescent : baseEnd_1763715 < baseStart_1763715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763760 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 12]
def baseStart_1763760 : Nat := 118140960795 + 1763760 * 2 ^ 59
def prefixEnd_1763760 : Nat := 4983230072969 + 3 ^ 40 * 1763760 * 2
def baseEnd_1763760 : Nat := 100628515463791612732069

theorem tailTrace_1763760 : CollatzResearch.WordTrace tailWord_1763760 prefixEnd_1763760 100628515463791612732069 := by
  unfold tailWord_1763760
  simp only [CollatzResearch.WordTrace]
  refine ⟨32164806045103110535632367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42886408060137480714176489 32164806045103110535632367)
  ·
    refine ⟨48247209067654665803448551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32164806045103110535632367 48247209067654665803448551)
    ·
      refine ⟨72370813601481998705172827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48247209067654665803448551 72370813601481998705172827)
      ·
        refine ⟨108556220402222998057759241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72370813601481998705172827 108556220402222998057759241)
        ·
          refine ⟨81417165301667248543319431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108556220402222998057759241 81417165301667248543319431)
          ·
            refine ⟨122125747952500872814979147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81417165301667248543319431 122125747952500872814979147)
            ·
              refine ⟨183188621928751309222468721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122125747952500872814979147 183188621928751309222468721)
              ·
                refine ⟨137391466446563481916851541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183188621928751309222468721 137391466446563481916851541)
                ·
                  refine ⟨100628515463791612732069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 137391466446563481916851541 100628515463791612732069)
                  ·
                    rfl

theorem cell23_1763760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 12].length) (baseStart_1763760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763760 prefixEnd_1763760 := by exact prefixLift 1763760
  have htrace : WordTrace (prefixWord ++ tailWord_1763760) baseStart_1763760 baseEnd_1763760 := by
    simpa [prefixWord, tailWord_1763760, baseEnd_1763760] using wordTrace_append hprefix tailTrace_1763760
  have hstable : (prefixWord ++ tailWord_1763760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763760).length < 2 ^ (prefixWord ++ tailWord_1763760).sum := by decide
  have hdescent : baseEnd_1763760 < baseStart_1763760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763774 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_1763774 : Nat := 118140960795 + 1763774 * 2 ^ 59
def prefixEnd_1763774 : Nat := 4983230072969 + 3 ^ 40 * 1763774 * 2
def baseEnd_1763774 : Nat := 905663827903287459813557

theorem tailTrace_1763774 : CollatzResearch.WordTrace tailWord_1763774 prefixEnd_1763774 905663827903287459813557 := by
  unfold tailWord_1763774
  simp only [CollatzResearch.WordTrace]
  refine ⟨8041265339019437682784297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42886748474770334308182917 8041265339019437682784297)
  ·
    refine ⟨6030949004264578262088223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8041265339019437682784297 6030949004264578262088223)
    ·
      refine ⟨9046423506396867393132335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6030949004264578262088223 9046423506396867393132335)
      ·
        refine ⟨13569635259595301089698503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9046423506396867393132335 13569635259595301089698503)
        ·
          refine ⟨20354452889392951634547755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13569635259595301089698503 20354452889392951634547755)
          ·
            refine ⟨30531679334089427451821633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20354452889392951634547755 30531679334089427451821633)
            ·
              refine ⟨22898759500567070588866225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30531679334089427451821633 22898759500567070588866225)
              ·
                refine ⟨17174069625425302941649669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22898759500567070588866225 17174069625425302941649669)
                ·
                  refine ⟨3220138054767244301559313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17174069625425302941649669 3220138054767244301559313)
                  ·
                    refine ⟨2415103541075433226169485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3220138054767244301559313 2415103541075433226169485)
                    ·
                      refine ⟨905663827903287459813557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2415103541075433226169485 905663827903287459813557)
                      ·
                        rfl

theorem cell23_1763774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_1763774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763774 prefixEnd_1763774 := by exact prefixLift 1763774
  have htrace : WordTrace (prefixWord ++ tailWord_1763774) baseStart_1763774 baseEnd_1763774 := by
    simpa [prefixWord, tailWord_1763774, baseEnd_1763774] using wordTrace_append hprefix tailTrace_1763774
  have hstable : (prefixWord ++ tailWord_1763774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763774).length < 2 ^ (prefixWord ++ tailWord_1763774).sum := by decide
  have hdescent : baseEnd_1763774 < baseStart_1763774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763788 : List Nat := [2, 2, 1, 4, 4, 1, 1, 1, 2, 1, 4]
def baseStart_1763788 : Nat := 118140960795 + 1763788 * 2 ^ 59
def prefixEnd_1763788 : Nat := 4983230072969 + 3 ^ 40 * 1763788 * 2
def baseEnd_1763788 : Nat := 905671016632450405038493

theorem tailTrace_1763788 : CollatzResearch.WordTrace tailWord_1763788 prefixEnd_1763788 905671016632450405038493 := by
  unfold tailWord_1763788
  simp only [CollatzResearch.WordTrace]
  refine ⟨32165316667052390926642009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42887088889403187902189345 32165316667052390926642009)
  ·
    refine ⟨24123987500289293194981507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32165316667052390926642009 24123987500289293194981507)
    ·
      refine ⟨36185981250433939792472261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24123987500289293194981507 36185981250433939792472261)
      ·
        refine ⟨6784871484456363711088549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36185981250433939792472261 6784871484456363711088549)
        ·
          refine ⟨1272163403335568195829103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6784871484456363711088549 1272163403335568195829103)
          ·
            refine ⟨1908245105003352293743655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1272163403335568195829103 1908245105003352293743655)
            ·
              refine ⟨2862367657505028440615483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1908245105003352293743655 2862367657505028440615483)
              ·
                refine ⟨4293551486257542660923225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2862367657505028440615483 4293551486257542660923225)
                ·
                  refine ⟨3220163614693156995692419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4293551486257542660923225 3220163614693156995692419)
                  ·
                    refine ⟨4830245422039735493538629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3220163614693156995692419 4830245422039735493538629)
                    ·
                      refine ⟨905671016632450405038493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4830245422039735493538629 905671016632450405038493)
                      ·
                        rfl

theorem cell23_1763788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_1763788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763788 prefixEnd_1763788 := by exact prefixLift 1763788
  have htrace : WordTrace (prefixWord ++ tailWord_1763788) baseStart_1763788 baseEnd_1763788 := by
    simpa [prefixWord, tailWord_1763788, baseEnd_1763788] using wordTrace_append hprefix tailTrace_1763788
  have hstable : (prefixWord ++ tailWord_1763788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763788).length < 2 ^ (prefixWord ++ tailWord_1763788).sum := by decide
  have hdescent : baseEnd_1763788 < baseStart_1763788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763811 : List Nat := [1, 1, 1, 6, 3, 2, 1, 2, 6]
def baseStart_1763811 : Nat := 118140960795 + 1763811 * 2 ^ 59
def prefixEnd_1763811 : Nat := 4983230072969 + 3 ^ 40 * 1763811 * 2
def baseEnd_1763811 : Nat := 100631425187500423894543

theorem tailTrace_1763811 : CollatzResearch.WordTrace tailWord_1763811 prefixEnd_1763811 100631425187500423894543 := by
  unfold tailWord_1763811
  simp only [CollatzResearch.WordTrace]
  refine ⟨64331472213021456781371287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42887648142014304520914191 64331472213021456781371287)
  ·
    refine ⟨96497208319532185172056931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64331472213021456781371287 96497208319532185172056931)
    ·
      refine ⟨144745812479298277758085397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96497208319532185172056931 144745812479298277758085397)
      ·
        refine ⟨6784959959967106769910253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 144745812479298277758085397 6784959959967106769910253)
        ·
          refine ⟨2544359984987665038716345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6784959959967106769910253 2544359984987665038716345)
          ·
            refine ⟨1908269988740748779037259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2544359984987665038716345 1908269988740748779037259)
            ·
              refine ⟨2862404983111123168555889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1908269988740748779037259 2862404983111123168555889)
              ·
                refine ⟨2146803737333342376416917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2862404983111123168555889 2146803737333342376416917)
                ·
                  refine ⟨100631425187500423894543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2146803737333342376416917 100631425187500423894543)
                  ·
                    rfl

theorem cell23_1763811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 6].length) (baseStart_1763811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763811 prefixEnd_1763811 := by exact prefixLift 1763811
  have htrace : WordTrace (prefixWord ++ tailWord_1763811) baseStart_1763811 baseEnd_1763811 := by
    simpa [prefixWord, tailWord_1763811, baseEnd_1763811] using wordTrace_append hprefix tailTrace_1763811
  have hstable : (prefixWord ++ tailWord_1763811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763811).length < 2 ^ (prefixWord ++ tailWord_1763811).sum := by decide
  have hdescent : baseEnd_1763811 < baseStart_1763811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763841 : List Nat := [1, 2, 4, 1, 3, 2, 2, 2, 1, 5]
def baseStart_1763841 : Nat := 118140960795 + 1763841 * 2 ^ 59
def prefixEnd_1763841 : Nat := 4983230072969 + 3 ^ 40 * 1763841 * 2
def baseEnd_1763841 : Nat := 301899410369046232558583

theorem tailTrace_1763841 : CollatzResearch.WordTrace tailWord_1763841 prefixEnd_1763841 301899410369046232558583 := by
  unfold tailWord_1763841
  simp only [CollatzResearch.WordTrace]
  refine ⟨64332566402912771904963377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42888377601941847936642251 64332566402912771904963377)
  ·
    refine ⟨48249424802184578928722533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64332566402912771904963377 48249424802184578928722533)
    ·
      refine ⟨9046767150409608549135475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48249424802184578928722533 9046767150409608549135475)
      ·
        refine ⟨13570150725614412823703213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9046767150409608549135475 13570150725614412823703213)
        ·
          refine ⟨5088806522105404808888705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13570150725614412823703213 5088806522105404808888705)
          ·
            refine ⟨3816604891579053606666529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5088806522105404808888705 3816604891579053606666529)
            ·
              refine ⟨2862453668684290204999897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3816604891579053606666529 2862453668684290204999897)
              ·
                refine ⟨2146840251513217653749923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2862453668684290204999897 2146840251513217653749923)
                ·
                  refine ⟨3220260377269826480624885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2146840251513217653749923 3220260377269826480624885)
                  ·
                    refine ⟨301899410369046232558583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3220260377269826480624885 301899410369046232558583)
                    ·
                      rfl

theorem cell23_1763841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_1763841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763841 prefixEnd_1763841 := by exact prefixLift 1763841
  have htrace : WordTrace (prefixWord ++ tailWord_1763841) baseStart_1763841 baseEnd_1763841 := by
    simpa [prefixWord, tailWord_1763841, baseEnd_1763841] using wordTrace_append hprefix tailTrace_1763841
  have hstable : (prefixWord ++ tailWord_1763841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763841).length < 2 ^ (prefixWord ++ tailWord_1763841).sum := by decide
  have hdescent : baseEnd_1763841 < baseStart_1763841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763864 : List Nat := [2, 1, 2, 3, 3, 1, 1, 3, 1, 1, 5]
def baseStart_1763864 : Nat := 118140960795 + 1763864 * 2 ^ 59
def prefixEnd_1763864 : Nat := 4983230072969 + 3 ^ 40 * 1763864 * 2
def baseEnd_1763864 : Nat := 905710041162192107688143

theorem tailTrace_1763864 : CollatzResearch.WordTrace tailWord_1763864 prefixEnd_1763864 905710041162192107688143 := by
  unfold tailWord_1763864
  simp only [CollatzResearch.WordTrace]
  refine ⟨32166702640914723416525323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42888936854552964555367097 32166702640914723416525323)
  ·
    refine ⟨48250053961372085124787985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32166702640914723416525323 48250053961372085124787985)
    ·
      refine ⟨36187540471029063843590989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48250053961372085124787985 36187540471029063843590989)
      ·
        refine ⟨13570327676635898941346621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36187540471029063843590989 13570327676635898941346621)
        ·
          refine ⟨5088872878738462103004983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13570327676635898941346621 5088872878738462103004983)
          ·
            refine ⟨7633309318107693154507475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5088872878738462103004983 7633309318107693154507475)
            ·
              refine ⟨11449963977161539731761213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7633309318107693154507475 11449963977161539731761213)
              ·
                refine ⟨4293736491435577399410455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11449963977161539731761213 4293736491435577399410455)
                ·
                  refine ⟨6440604737153366099115683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4293736491435577399410455 6440604737153366099115683)
                  ·
                    refine ⟨9660907105730049148673525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6440604737153366099115683 9660907105730049148673525)
                    ·
                      refine ⟨905710041162192107688143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9660907105730049148673525 905710041162192107688143)
                      ·
                        rfl

theorem cell23_1763864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_1763864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763864 prefixEnd_1763864 := by exact prefixLift 1763864
  have htrace : WordTrace (prefixWord ++ tailWord_1763864) baseStart_1763864 baseEnd_1763864 := by
    simpa [prefixWord, tailWord_1763864, baseEnd_1763864] using wordTrace_append hprefix tailTrace_1763864
  have hstable : (prefixWord ++ tailWord_1763864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763864).length < 2 ^ (prefixWord ++ tailWord_1763864).sum := by decide
  have hdescent : baseEnd_1763864 < baseStart_1763864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763872 : List Nat := [2, 1, 1, 6, 2, 1, 3, 2, 1, 1, 3]
def baseStart_1763872 : Nat := 118140960795 + 1763872 * 2 ^ 59
def prefixEnd_1763872 : Nat := 4983230072969 + 3 ^ 40 * 1763872 * 2
def baseEnd_1763872 : Nat := 905714149007428076388107

theorem tailTrace_1763872 : CollatzResearch.WordTrace tailWord_1763872 prefixEnd_1763872 905714149007428076388107 := by
  unfold tailWord_1763872
  simp only [CollatzResearch.WordTrace]
  refine ⟨32166848532900232099670935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42889131377200309466227913 32166848532900232099670935)
  ·
    refine ⟨48250272799350348149506403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32166848532900232099670935 48250272799350348149506403)
    ·
      refine ⟨72375409199025522224259605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48250272799350348149506403 72375409199025522224259605)
      ·
        refine ⟨3392597306204321354262169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72375409199025522224259605 3392597306204321354262169)
        ·
          refine ⟨2544447979653241015696627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3392597306204321354262169 2544447979653241015696627)
          ·
            refine ⟨3816671969479861523544941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2544447979653241015696627 3816671969479861523544941)
            ·
              refine ⟨1431251988554948071329353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3816671969479861523544941 1431251988554948071329353)
              ·
                refine ⟨1073438991416211053497015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1431251988554948071329353 1073438991416211053497015)
                ·
                  refine ⟨1610158487124316580245523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1073438991416211053497015 1610158487124316580245523)
                  ·
                    refine ⟨2415237730686474870368285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1610158487124316580245523 2415237730686474870368285)
                    ·
                      refine ⟨905714149007428076388107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2415237730686474870368285 905714149007428076388107)
                      ·
                        rfl

theorem cell23_1763872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_1763872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763872 prefixEnd_1763872 := by exact prefixLift 1763872
  have htrace : WordTrace (prefixWord ++ tailWord_1763872) baseStart_1763872 baseEnd_1763872 := by
    simpa [prefixWord, tailWord_1763872, baseEnd_1763872] using wordTrace_append hprefix tailTrace_1763872
  have hstable : (prefixWord ++ tailWord_1763872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763872).length < 2 ^ (prefixWord ++ tailWord_1763872).sum := by decide
  have hdescent : baseEnd_1763872 < baseStart_1763872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763892 : List Nat := [2, 5, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_1763892 : Nat := 118140960795 + 1763892 * 2 ^ 59
def prefixEnd_1763892 : Nat := 4983230072969 + 3 ^ 40 * 1763892 * 2
def baseEnd_1763892 : Nat := 301908139540172666046005

theorem tailTrace_1763892 : CollatzResearch.WordTrace tailWord_1763892 prefixEnd_1763892 301908139540172666046005 := by
  unfold tailWord_1763892
  simp only [CollatzResearch.WordTrace]
  refine ⟨32167213262864003807534965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42889617683818671743379953 32167213262864003807534965)
  ·
    refine ⟨3015676243393500356956403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32167213262864003807534965 3015676243393500356956403)
    ·
      refine ⟨4523514365090250535434605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3015676243393500356956403 4523514365090250535434605)
      ·
        refine ⟨1696317886908843950787977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4523514365090250535434605 1696317886908843950787977)
        ·
          refine ⟨1272238415181632963090983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1696317886908843950787977 1272238415181632963090983)
          ·
            refine ⟨1908357622772449444636475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1272238415181632963090983 1908357622772449444636475)
            ·
              refine ⟨2862536434158674166954713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1908357622772449444636475 2862536434158674166954713)
              ·
                refine ⟨2146902325619005625216035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2862536434158674166954713 2146902325619005625216035)
                ·
                  refine ⟨3220353488428508437824053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2146902325619005625216035 3220353488428508437824053)
                  ·
                    refine ⟨301908139540172666046005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3220353488428508437824053 301908139540172666046005)
                    ·
                      rfl

theorem cell23_1763892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_1763892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763892 prefixEnd_1763892 := by exact prefixLift 1763892
  have htrace : WordTrace (prefixWord ++ tailWord_1763892) baseStart_1763892 baseEnd_1763892 := by
    simpa [prefixWord, tailWord_1763892, baseEnd_1763892] using wordTrace_append hprefix tailTrace_1763892
  have hstable : (prefixWord ++ tailWord_1763892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763892).length < 2 ^ (prefixWord ++ tailWord_1763892).sum := by decide
  have hdescent : baseEnd_1763892 < baseStart_1763892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763898 : List Nat := [3, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3]
def baseStart_1763898 : Nat := 118140960795 + 1763898 * 2 ^ 59
def prefixEnd_1763898 : Nat := 4983230072969 + 3 ^ 40 * 1763898 * 2
def baseEnd_1763898 : Nat := 905727499504444974662987

theorem tailTrace_1763898 : CollatzResearch.WordTrace tailWord_1763898 prefixEnd_1763898 905727499504444974662987 := by
  unfold tailWord_1763898
  simp only [CollatzResearch.WordTrace]
  refine ⟨16083661340926567659947087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42889763575804180426525565 16083661340926567659947087)
  ·
    refine ⟨24125492011389851489920631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16083661340926567659947087 24125492011389851489920631)
    ·
      refine ⟨36188238017084777234880947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24125492011389851489920631 36188238017084777234880947)
      ·
        refine ⟨54282357025627165852321421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36188238017084777234880947 54282357025627165852321421)
        ·
          refine ⟨20355883884610187194620533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54282357025627165852321421 20355883884610187194620533)
          ·
            refine ⟨1908364114182205049495675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20355883884610187194620533 1908364114182205049495675)
            ·
              refine ⟨2862546171273307574243513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1908364114182205049495675 2862546171273307574243513)
              ·
                refine ⟨2146909628454980680682635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2862546171273307574243513 2146909628454980680682635)
                ·
                  refine ⟨3220364442682471021023953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2146909628454980680682635 3220364442682471021023953)
                  ·
                    refine ⟨2415273332011853265767965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3220364442682471021023953 2415273332011853265767965)
                    ·
                      refine ⟨905727499504444974662987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2415273332011853265767965 905727499504444974662987)
                      ·
                        rfl

theorem cell23_1763898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3].length) (baseStart_1763898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763898 prefixEnd_1763898 := by exact prefixLift 1763898
  have htrace : WordTrace (prefixWord ++ tailWord_1763898) baseStart_1763898 baseEnd_1763898 := by
    simpa [prefixWord, tailWord_1763898, baseEnd_1763898] using wordTrace_append hprefix tailTrace_1763898
  have hstable : (prefixWord ++ tailWord_1763898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763898).length < 2 ^ (prefixWord ++ tailWord_1763898).sum := by decide
  have hdescent : baseEnd_1763898 < baseStart_1763898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763907 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 5]
def baseStart_1763907 : Nat := 118140960795 + 1763907 * 2 ^ 59
def prefixEnd_1763907 : Nat := 4983230072969 + 3 ^ 40 * 1763907 * 2
def baseEnd_1763907 : Nat := 905732120830335439450445

theorem tailTrace_1763907 : CollatzResearch.WordTrace tailWord_1763907 prefixEnd_1763907 905732120830335439450445 := by
  unfold tailWord_1763907
  simp only [CollatzResearch.WordTrace]
  refine ⟨64334973620673665176865975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42889982413782443451243983 64334973620673665176865975)
  ·
    refine ⟨96502460431010497765298963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64334973620673665176865975 96502460431010497765298963)
    ·
      refine ⟨144753690646515746647948445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96502460431010497765298963 144753690646515746647948445)
      ·
        refine ⟨54282633992443404992980667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144753690646515746647948445 54282633992443404992980667)
        ·
          refine ⟨81423950988665107489471001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54282633992443404992980667 81423950988665107489471001)
          ·
            refine ⟨61067963241498830617103251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81423950988665107489471001 61067963241498830617103251)
            ·
              refine ⟨91601944862248245925654877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61067963241498830617103251 91601944862248245925654877)
              ·
                refine ⟨34350729323343092222120579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91601944862248245925654877 34350729323343092222120579)
                ·
                  refine ⟨51526093985014638333180869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34350729323343092222120579 51526093985014638333180869)
                  ·
                    refine ⟨9661142622190244687471413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51526093985014638333180869 9661142622190244687471413)
                    ·
                      refine ⟨905732120830335439450445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9661142622190244687471413 905732120830335439450445)
                      ·
                        rfl

theorem cell23_1763907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_1763907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763907 prefixEnd_1763907 := by exact prefixLift 1763907
  have htrace : WordTrace (prefixWord ++ tailWord_1763907) baseStart_1763907 baseEnd_1763907 := by
    simpa [prefixWord, tailWord_1763907, baseEnd_1763907] using wordTrace_append hprefix tailTrace_1763907
  have hstable : (prefixWord ++ tailWord_1763907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763907).length < 2 ^ (prefixWord ++ tailWord_1763907).sum := by decide
  have hdescent : baseEnd_1763907 < baseStart_1763907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763911 : List Nat := [1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 3]
def baseStart_1763911 : Nat := 118140960795 + 1763911 * 2 ^ 59
def prefixEnd_1763911 : Nat := 4983230072969 + 3 ^ 40 * 1763911 * 2
def baseEnd_1763911 : Nat := 905734174752953423800427

theorem tailTrace_1763911 : CollatzResearch.WordTrace tailWord_1763911 prefixEnd_1763911 905734174752953423800427 := by
  unfold tailWord_1763911
  simp only [CollatzResearch.WordTrace]
  refine ⟨64335119512659173860011587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42890079675106115906674391 64335119512659173860011587)
  ·
    refine ⟨96502679268988760790017381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64335119512659173860011587 96502679268988760790017381)
    ·
      refine ⟨18094252362935392648128259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96502679268988760790017381 18094252362935392648128259)
      ·
        refine ⟨27141378544403088972192389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18094252362935392648128259 27141378544403088972192389)
        ·
          refine ⟨5089008477075579182286073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27141378544403088972192389 5089008477075579182286073)
          ·
            refine ⟨3816756357806684386714555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5089008477075579182286073 3816756357806684386714555)
            ·
              refine ⟨5725134536710026580071833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3816756357806684386714555 5725134536710026580071833)
              ·
                refine ⟨4293850902532519935053875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5725134536710026580071833 4293850902532519935053875)
                ·
                  refine ⟨6440776353798779902580813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4293850902532519935053875 6440776353798779902580813)
                  ·
                    refine ⟨2415291132674542463467805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6440776353798779902580813 2415291132674542463467805)
                    ·
                      refine ⟨905734174752953423800427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2415291132674542463467805 905734174752953423800427)
                      ·
                        rfl

theorem cell23_1763911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_1763911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763911 prefixEnd_1763911 := by exact prefixLift 1763911
  have htrace : WordTrace (prefixWord ++ tailWord_1763911) baseStart_1763911 baseEnd_1763911 := by
    simpa [prefixWord, tailWord_1763911, baseEnd_1763911] using wordTrace_append hprefix tailTrace_1763911
  have hstable : (prefixWord ++ tailWord_1763911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763911).length < 2 ^ (prefixWord ++ tailWord_1763911).sum := by decide
  have hdescent : baseEnd_1763911 < baseStart_1763911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763951 : List Nat := [1, 1, 2, 1, 3, 2, 3, 3, 1, 4, 2]
def baseStart_1763951 : Nat := 118140960795 + 1763951 * 2 ^ 59
def prefixEnd_1763951 : Nat := 4983230072969 + 3 ^ 40 * 1763951 * 2
def baseEnd_1763951 : Nat := 905754713979133267300243

theorem tailTrace_1763951 : CollatzResearch.WordTrace tailWord_1763951 prefixEnd_1763951 905754713979133267300243 := by
  unfold tailWord_1763951
  simp only [CollatzResearch.WordTrace]
  refine ⟨64336578432514260691467707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42891052288342840460978471 64336578432514260691467707)
  ·
    refine ⟨96504867648771391037201561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64336578432514260691467707 96504867648771391037201561)
    ·
      refine ⟨72378650736578543277901171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96504867648771391037201561 72378650736578543277901171)
      ·
        refine ⟨108567976104867814916851757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72378650736578543277901171 108567976104867814916851757)
        ·
          refine ⟨40712991039325430593819409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108567976104867814916851757 40712991039325430593819409)
          ·
            refine ⟨30534743279494072945364557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40712991039325430593819409 30534743279494072945364557)
            ·
              refine ⟨11450528729810277354511709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30534743279494072945364557 11450528729810277354511709)
              ·
                refine ⟨4293948273678854007941891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11450528729810277354511709 4293948273678854007941891)
                ·
                  refine ⟨6440922410518281011912837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4293948273678854007941891 6440922410518281011912837)
                  ·
                    refine ⟨1207672951972177689733657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6440922410518281011912837 1207672951972177689733657)
                    ·
                      refine ⟨905754713979133267300243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1207672951972177689733657 905754713979133267300243)
                      ·
                        rfl

theorem cell23_1763951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 4, 2].length) (baseStart_1763951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763951 prefixEnd_1763951 := by exact prefixLift 1763951
  have htrace : WordTrace (prefixWord ++ tailWord_1763951) baseStart_1763951 baseEnd_1763951 := by
    simpa [prefixWord, tailWord_1763951, baseEnd_1763951] using wordTrace_append hprefix tailTrace_1763951
  have hstable : (prefixWord ++ tailWord_1763951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763951).length < 2 ^ (prefixWord ++ tailWord_1763951).sum := by decide
  have hdescent : baseEnd_1763951 < baseStart_1763951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763972 : List Nat := [2, 3, 2, 1, 3, 3, 2, 1, 1, 3, 2]
def baseStart_1763972 : Nat := 118140960795 + 1763972 * 2 ^ 59
def prefixEnd_1763972 : Nat := 4983230072969 + 3 ^ 40 * 1763972 * 2
def baseEnd_1763972 : Nat := 905765497072877685137647

theorem tailTrace_1763972 : CollatzResearch.WordTrace tailWord_1763972 prefixEnd_1763972 905765497072877685137647 := by
  unfold tailWord_1763972
  simp only [CollatzResearch.WordTrace]
  refine ⟨32168672182719090638991085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42891562910292120851988113 32168672182719090638991085)
  ·
    refine ⟨12063252068519658989621657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32168672182719090638991085 12063252068519658989621657)
    ·
      refine ⟨9047439051389744242216243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12063252068519658989621657 9047439051389744242216243)
      ·
        refine ⟨13571158577084616363324365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9047439051389744242216243 13571158577084616363324365)
        ·
          refine ⟨5089184466406731136246637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13571158577084616363324365 5089184466406731136246637)
          ·
            refine ⟨1908444174902524176092489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5089184466406731136246637 1908444174902524176092489)
            ·
              refine ⟨1431333131176893132069367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1908444174902524176092489 1431333131176893132069367)
              ·
                refine ⟨2146999696765339698104051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1431333131176893132069367 2146999696765339698104051)
                ·
                  refine ⟨3220499545148009547156077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2146999696765339698104051 3220499545148009547156077)
                  ·
                    refine ⟨1207687329430503580183529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3220499545148009547156077 1207687329430503580183529)
                    ·
                      refine ⟨905765497072877685137647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1207687329430503580183529 905765497072877685137647)
                      ·
                        rfl

theorem cell23_1763972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_1763972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763972 prefixEnd_1763972 := by exact prefixLift 1763972
  have htrace : WordTrace (prefixWord ++ tailWord_1763972) baseStart_1763972 baseEnd_1763972 := by
    simpa [prefixWord, tailWord_1763972, baseEnd_1763972] using wordTrace_append hprefix tailTrace_1763972
  have hstable : (prefixWord ++ tailWord_1763972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763972).length < 2 ^ (prefixWord ++ tailWord_1763972).sum := by decide
  have hdescent : baseEnd_1763972 < baseStart_1763972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763991 : List Nat := [1, 1, 3, 3, 2, 1, 1, 6, 5]
def baseStart_1763991 : Nat := 118140960795 + 1763991 * 2 ^ 59
def prefixEnd_1763991 : Nat := 4983230072969 + 3 ^ 40 * 1763991 * 2
def baseEnd_1763991 : Nat := 100641694800590345644451

theorem tailTrace_1763991 : CollatzResearch.WordTrace tailWord_1763991 prefixEnd_1763991 100641694800590345644451 := by
  unfold tailWord_1763991
  simp only [CollatzResearch.WordTrace]
  refine ⟨64338037352369347522923827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42892024901579565015282551 64338037352369347522923827)
  ·
    refine ⟨96507056028554021284385741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64338037352369347522923827 96507056028554021284385741)
    ·
      refine ⟨36190146010707757981644653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96507056028554021284385741 36190146010707757981644653)
      ·
        refine ⟨13571304754015409243116745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36190146010707757981644653 13571304754015409243116745)
        ·
          refine ⟨10178478565511556932337559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13571304754015409243116745 10178478565511556932337559)
          ·
            refine ⟨15267717848267335398506339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10178478565511556932337559 15267717848267335398506339)
            ·
              refine ⟨22901576772401003097759509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15267717848267335398506339 22901576772401003097759509)
              ·
                refine ⟨1073511411206297020207477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22901576772401003097759509 1073511411206297020207477)
                ·
                  refine ⟨100641694800590345644451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1073511411206297020207477 100641694800590345644451)
                  ·
                    rfl

theorem cell23_1763991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 5].length) (baseStart_1763991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1763991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1763991 prefixEnd_1763991 := by exact prefixLift 1763991
  have htrace : WordTrace (prefixWord ++ tailWord_1763991) baseStart_1763991 baseEnd_1763991 := by
    simpa [prefixWord, tailWord_1763991, baseEnd_1763991] using wordTrace_append hprefix tailTrace_1763991
  have hstable : (prefixWord ++ tailWord_1763991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763991).length < 2 ^ (prefixWord ++ tailWord_1763991).sum := by decide
  have hdescent : baseEnd_1763991 < baseStart_1763991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764004 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 3, 7]
def baseStart_1764004 : Nat := 118140960795 + 1764004 * 2 ^ 59
def prefixEnd_1764004 : Nat := 4983230072969 + 3 ^ 40 * 1764004 * 2
def baseEnd_1764004 : Nat := 301927309484607186645833

theorem tailTrace_1764004 : CollatzResearch.WordTrace tailWord_1764004 prefixEnd_1764004 301927309484607186645833 := by
  unfold tailWord_1764004
  simp only [CollatzResearch.WordTrace]
  refine ⟨32169255750661125371573533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42892341000881500495431377 32169255750661125371573533)
  ·
    refine ⟨12063470906497922014340075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32169255750661125371573533 12063470906497922014340075)
    ·
      refine ⟨18095206359746883021510113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12063470906497922014340075 18095206359746883021510113)
      ·
        refine ⟨13571404769810162266132585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18095206359746883021510113 13571404769810162266132585)
        ·
          refine ⟨10178553577357621699599439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13571404769810162266132585 10178553577357621699599439)
          ·
            refine ⟨15267830366036432549399159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10178553577357621699599439 15267830366036432549399159)
            ·
              refine ⟨22901745549054648824098739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15267830366036432549399159 22901745549054648824098739)
              ·
                refine ⟨34352618323581973236148109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22901745549054648824098739 34352618323581973236148109)
                ·
                  refine ⟨12882231871343239963555541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34352618323581973236148109 12882231871343239963555541)
                  ·
                    refine ⟨301927309484607186645833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12882231871343239963555541 301927309484607186645833)
                    ·
                      rfl

theorem cell23_1764004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_1764004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764004 prefixEnd_1764004 := by exact prefixLift 1764004
  have htrace : WordTrace (prefixWord ++ tailWord_1764004) baseStart_1764004 baseEnd_1764004 := by
    simpa [prefixWord, tailWord_1764004, baseEnd_1764004] using wordTrace_append hprefix tailTrace_1764004
  have hstable : (prefixWord ++ tailWord_1764004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764004).length < 2 ^ (prefixWord ++ tailWord_1764004).sum := by decide
  have hdescent : baseEnd_1764004 < baseStart_1764004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764021 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 1, 7]
def baseStart_1764021 : Nat := 118140960795 + 1764021 * 2 ^ 59
def prefixEnd_1764021 : Nat := 4983230072969 + 3 ^ 40 * 1764021 * 2
def baseEnd_1764021 : Nat := 301930219208315997808307

theorem tailTrace_1764021 : CollatzResearch.WordTrace tailWord_1764021 prefixEnd_1764021 301930219208315997808307 := by
  unfold tailWord_1764021
  simp only [CollatzResearch.WordTrace]
  refine ⟨64339131542260662646515917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42892754361507108431010611 64339131542260662646515917)
  ·
    refine ⟨24127174328347748492443469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64339131542260662646515917 24127174328347748492443469)
    ·
      refine ⟨9047690373130405684666301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24127174328347748492443469 9047690373130405684666301)
      ·
        refine ⟨3392883889923902131749863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9047690373130405684666301 3392883889923902131749863)
        ·
          refine ⟨5089325834885853197624795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3392883889923902131749863 5089325834885853197624795)
          ·
            refine ⟨7633988752328779796437193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5089325834885853197624795 7633988752328779796437193)
            ·
              refine ⟨5725491564246584847327895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7633988752328779796437193 5725491564246584847327895)
              ·
                refine ⟨8588237346369877270991843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5725491564246584847327895 8588237346369877270991843)
                ·
                  refine ⟨12882356019554815906487765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8588237346369877270991843 12882356019554815906487765)
                  ·
                    refine ⟨301930219208315997808307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12882356019554815906487765 301930219208315997808307)
                    ·
                      rfl

theorem cell23_1764021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_1764021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764021 prefixEnd_1764021 := by exact prefixLift 1764021
  have htrace : WordTrace (prefixWord ++ tailWord_1764021) baseStart_1764021 baseEnd_1764021 := by
    simpa [prefixWord, tailWord_1764021, baseEnd_1764021] using wordTrace_append hprefix tailTrace_1764021
  have hstable : (prefixWord ++ tailWord_1764021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764021).length < 2 ^ (prefixWord ++ tailWord_1764021).sum := by decide
  have hdescent : baseEnd_1764021 < baseStart_1764021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764078 : List Nat := [4, 1, 2, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_1764078 : Nat := 118140960795 + 1764078 * 2 ^ 59
def prefixEnd_1764078 : Nat := 4983230072969 + 3 ^ 40 * 1764078 * 2
def baseEnd_1764078 : Nat := 905819926022254270412159

theorem tailTrace_1764078 : CollatzResearch.WordTrace tailWord_1764078 prefixEnd_1764078 905819926022254270412159 := by
  unfold tailWord_1764078
  simp only [CollatzResearch.WordTrace]
  refine ⟨8042651312881770172667611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42894140335369440920893925 8042651312881770172667611)
  ·
    refine ⟨12063976969322655259001417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8042651312881770172667611 12063976969322655259001417)
    ·
      refine ⟨9047982726991991444251063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12063976969322655259001417 9047982726991991444251063)
      ·
        refine ⟨13571974090487987166376595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9047982726991991444251063 13571974090487987166376595)
        ·
          refine ⟨20357961135731980749564893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13571974090487987166376595 20357961135731980749564893)
          ·
            refine ⟨7634235425899492781086835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20357961135731980749564893 7634235425899492781086835)
            ·
              refine ⟨11451353138849239171630253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7634235425899492781086835 11451353138849239171630253)
              ·
                refine ⟨4294257427068464689361345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11451353138849239171630253 4294257427068464689361345)
                ·
                  refine ⟨3220693070301348517021009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4294257427068464689361345 3220693070301348517021009)
                  ·
                    refine ⟨2415519802726011387765757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3220693070301348517021009 2415519802726011387765757)
                    ·
                      refine ⟨905819926022254270412159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2415519802726011387765757 905819926022254270412159)
                      ·
                        rfl

theorem cell23_1764078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_1764078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764078 prefixEnd_1764078 := by exact prefixLift 1764078
  have htrace : WordTrace (prefixWord ++ tailWord_1764078) baseStart_1764078 baseEnd_1764078 := by
    simpa [prefixWord, tailWord_1764078, baseEnd_1764078] using wordTrace_append hprefix tailTrace_1764078
  have hstable : (prefixWord ++ tailWord_1764078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764078).length < 2 ^ (prefixWord ++ tailWord_1764078).sum := by decide
  have hdescent : baseEnd_1764078 < baseStart_1764078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764098 : List Nat := [3, 4, 1, 1, 1, 2, 1, 4, 6]
def baseStart_1764098 : Nat := 118140960795 + 1764098 * 2 ^ 59
def prefixEnd_1764098 : Nat := 4983230072969 + 3 ^ 40 * 1764098 * 2
def baseEnd_1764098 : Nat := 100647799515038243573563

theorem tailTrace_1764098 : CollatzResearch.WordTrace tailWord_1764098 prefixEnd_1764098 100647799515038243573563 := by
  unfold tailWord_1764098
  simp only [CollatzResearch.WordTrace]
  refine ⟨16085484990745426199267237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42894626641987803198045965 16085484990745426199267237)
  ·
    refine ⟨3016028435764767412362607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16085484990745426199267237 3016028435764767412362607)
    ·
      refine ⟨4524042653647151118543911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3016028435764767412362607 4524042653647151118543911)
      ·
        refine ⟨6786063980470726677815867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4524042653647151118543911 6786063980470726677815867)
        ·
          refine ⟨10179095970706090016723801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6786063980470726677815867 10179095970706090016723801)
          ·
            refine ⟨7634321978029567512542851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10179095970706090016723801 7634321978029567512542851)
            ·
              refine ⟨11451482967044351268814277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7634321978029567512542851 11451482967044351268814277)
              ·
                refine ⟨2147153056320815862902677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11451482967044351268814277 2147153056320815862902677)
                ·
                  refine ⟨100647799515038243573563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2147153056320815862902677 100647799515038243573563)
                  ·
                    rfl

theorem cell23_1764098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_1764098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764098 prefixEnd_1764098 := by exact prefixLift 1764098
  have htrace : WordTrace (prefixWord ++ tailWord_1764098) baseStart_1764098 baseEnd_1764098 := by
    simpa [prefixWord, tailWord_1764098, baseEnd_1764098] using wordTrace_append hprefix tailTrace_1764098
  have hstable : (prefixWord ++ tailWord_1764098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764098).length < 2 ^ (prefixWord ++ tailWord_1764098).sum := by decide
  have hdescent : baseEnd_1764098 < baseStart_1764098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764108 : List Nat := [2, 2, 1, 2, 2, 1, 1, 5, 3, 1, 3]
def baseStart_1764108 : Nat := 118140960795 + 1764108 * 2 ^ 59
def prefixEnd_1764108 : Nat := 4983230072969 + 3 ^ 40 * 1764108 * 2
def baseEnd_1764108 : Nat := 905835330441889153037021

theorem tailTrace_1764108 : CollatzResearch.WordTrace tailWord_1764108 prefixEnd_1764108 905835330441889153037021 := by
  unfold tailWord_1764108
  simp only [CollatzResearch.WordTrace]
  refine ⟨32171152346472738252466489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42894869795296984336621985 32171152346472738252466489)
  ·
    refine ⟨24128364259854553689349867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32171152346472738252466489 24128364259854553689349867)
    ·
      refine ⟨36192546389781830534024801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24128364259854553689349867 36192546389781830534024801)
      ·
        refine ⟨27144409792336372900518601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36192546389781830534024801 27144409792336372900518601)
        ·
          refine ⟨20358307344252279675388951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27144409792336372900518601 20358307344252279675388951)
          ·
            refine ⟨30537461016378419513083427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20358307344252279675388951 30537461016378419513083427)
            ·
              refine ⟨45806191524567629269625141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30537461016378419513083427 45806191524567629269625141)
              ·
                refine ⟨4294330455428215244027357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45806191524567629269625141 4294330455428215244027357)
                ·
                  refine ⟨1610373920785580716510259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4294330455428215244027357 1610373920785580716510259)
                  ·
                    refine ⟨2415560881178371074765389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1610373920785580716510259 2415560881178371074765389)
                    ·
                      refine ⟨905835330441889153037021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2415560881178371074765389 905835330441889153037021)
                      ·
                        rfl

theorem cell23_1764108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_1764108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764108 prefixEnd_1764108 := by exact prefixLift 1764108
  have htrace : WordTrace (prefixWord ++ tailWord_1764108) baseStart_1764108 baseEnd_1764108 := by
    simpa [prefixWord, tailWord_1764108, baseEnd_1764108] using wordTrace_append hprefix tailTrace_1764108
  have hstable : (prefixWord ++ tailWord_1764108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764108).length < 2 ^ (prefixWord ++ tailWord_1764108).sum := by decide
  have hdescent : baseEnd_1764108 < baseStart_1764108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764151 : List Nat := [1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 5]
def baseStart_1764151 : Nat := 118140960795 + 1764151 * 2 ^ 59
def prefixEnd_1764151 : Nat := 4983230072969 + 3 ^ 40 * 1764151 * 2
def baseEnd_1764151 : Nat := 905857410110032484799323

theorem tailTrace_1764151 : CollatzResearch.WordTrace tailWord_1764151 prefixEnd_1764151 905857410110032484799323 := by
  unfold tailWord_1764151
  simp only [CollatzResearch.WordTrace]
  refine ⟨64343873031789694848748307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42895915354526463232498871 64343873031789694848748307)
  ·
    refine ⟨96515809547684542273122461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64343873031789694848748307 96515809547684542273122461)
    ·
      refine ⟨36193428580381703352420923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96515809547684542273122461 36193428580381703352420923)
      ·
        refine ⟨54290142870572555028631385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36193428580381703352420923 54290142870572555028631385)
        ·
          refine ⟨40717607152929416271473539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54290142870572555028631385 40717607152929416271473539)
          ·
            refine ⟨61076410729394124407210309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40717607152929416271473539 61076410729394124407210309)
            ·
              refine ⟨11451827011761398326351933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61076410729394124407210309 11451827011761398326351933)
              ·
                refine ⟨4294435129410524372381975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11451827011761398326351933 4294435129410524372381975)
                ·
                  refine ⟨6441652694115786558572963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4294435129410524372381975 6441652694115786558572963)
                  ·
                    refine ⟨9662479041173679837859445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6441652694115786558572963 9662479041173679837859445)
                    ·
                      refine ⟨905857410110032484799323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9662479041173679837859445 905857410110032484799323)
                      ·
                        rfl

theorem cell23_1764151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_1764151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764151 prefixEnd_1764151 := by exact prefixLift 1764151
  have htrace : WordTrace (prefixWord ++ tailWord_1764151) baseStart_1764151 baseEnd_1764151 := by
    simpa [prefixWord, tailWord_1764151, baseEnd_1764151] using wordTrace_append hprefix tailTrace_1764151
  have hstable : (prefixWord ++ tailWord_1764151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764151).length < 2 ^ (prefixWord ++ tailWord_1764151).sum := by decide
  have hdescent : baseEnd_1764151 < baseStart_1764151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764185 : List Nat := [1, 2, 1, 2, 2, 5, 2, 2, 1, 2, 3]
def baseStart_1764185 : Nat := 118140960795 + 1764185 * 2 ^ 59
def prefixEnd_1764185 : Nat := 4983230072969 + 3 ^ 40 * 1764185 * 2
def baseEnd_1764185 : Nat := 905874868452285351774167

theorem tailTrace_1764185 : CollatzResearch.WordTrace tailWord_1764185 prefixEnd_1764185 905874868452285351774167 := by
  unfold tailWord_1764185
  simp only [CollatzResearch.WordTrace]
  refine ⟨64345113113666518655486009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42896742075777679103657339 64345113113666518655486009)
  ·
    refine ⟨48258834835249888991614507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64345113113666518655486009 48258834835249888991614507)
    ·
      refine ⟨72388252252874833487421761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48258834835249888991614507 72388252252874833487421761)
      ·
        refine ⟨54291189189656125115566321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72388252252874833487421761 54291189189656125115566321)
        ·
          refine ⟨40718391892242093836674741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54291189189656125115566321 40718391892242093836674741)
          ·
            refine ⟨3817349239897696297188257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40718391892242093836674741 3817349239897696297188257)
            ·
              refine ⟨2863011929923272222891193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3817349239897696297188257 2863011929923272222891193)
              ·
                refine ⟨2147258947442454167168395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2863011929923272222891193 2147258947442454167168395)
                ·
                  refine ⟨3220888421163681250752593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2147258947442454167168395 3220888421163681250752593)
                  ·
                    refine ⟨2415666315872760938064445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3220888421163681250752593 2415666315872760938064445)
                    ·
                      refine ⟨905874868452285351774167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2415666315872760938064445 905874868452285351774167)
                      ·
                        rfl

theorem cell23_1764185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 2, 3].length) (baseStart_1764185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764185 prefixEnd_1764185 := by exact prefixLift 1764185
  have htrace : WordTrace (prefixWord ++ tailWord_1764185) baseStart_1764185 baseEnd_1764185 := by
    simpa [prefixWord, tailWord_1764185, baseEnd_1764185] using wordTrace_append hprefix tailTrace_1764185
  have hstable : (prefixWord ++ tailWord_1764185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764185).length < 2 ^ (prefixWord ++ tailWord_1764185).sum := by decide
  have hdescent : baseEnd_1764185 < baseStart_1764185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764188 : List Nat := [2, 2, 4, 2, 1, 2, 1, 9]
def baseStart_1764188 : Nat := 118140960795 + 1764188 * 2 ^ 59
def prefixEnd_1764188 : Nat := 4983230072969 + 3 ^ 40 * 1764188 * 2
def baseEnd_1764188 : Nat := 33550978107194401482839

theorem tailTrace_1764188 : CollatzResearch.WordTrace tailWord_1764188 prefixEnd_1764188 33550978107194401482839 := by
  unfold tailWord_1764188
  simp only [CollatzResearch.WordTrace]
  refine ⟨32172611266327825083922609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42896815021770433445230145 32172611266327825083922609)
  ·
    refine ⟨24129458449745868812941957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32172611266327825083922609 24129458449745868812941957)
    ·
      refine ⟨4524273459327350402426617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24129458449745868812941957 4524273459327350402426617)
      ·
        refine ⟨3393205094495512801819963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4524273459327350402426617 3393205094495512801819963)
        ·
          refine ⟨5089807641743269202729945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3393205094495512801819963 5089807641743269202729945)
          ·
            refine ⟨3817355731307451902047459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5089807641743269202729945 3817355731307451902047459)
            ·
              refine ⟨5726033596961177853071189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3817355731307451902047459 5726033596961177853071189)
              ·
                refine ⟨33550978107194401482839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5726033596961177853071189 33550978107194401482839)
                ·
                  rfl

theorem cell23_1764188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 9].length) (baseStart_1764188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764188 prefixEnd_1764188 := by exact prefixLift 1764188
  have htrace : WordTrace (prefixWord ++ tailWord_1764188) baseStart_1764188 baseEnd_1764188 := by
    simpa [prefixWord, tailWord_1764188, baseEnd_1764188] using wordTrace_append hprefix tailTrace_1764188
  have hstable : (prefixWord ++ tailWord_1764188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764188).length < 2 ^ (prefixWord ++ tailWord_1764188).sum := by decide
  have hdescent : baseEnd_1764188 < baseStart_1764188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764199 : List Nat := [1, 1, 5, 1, 2, 2, 3, 3, 1, 2, 2]
def baseStart_1764199 : Nat := 118140960795 + 1764199 * 2 ^ 59
def prefixEnd_1764199 : Nat := 4983230072969 + 3 ^ 40 * 1764199 * 2
def baseEnd_1764199 : Nat := 905882057181448296999103

theorem tailTrace_1764199 : CollatzResearch.WordTrace tailWord_1764199 prefixEnd_1764199 905882057181448296999103 := by
  unfold tailWord_1764199
  simp only [CollatzResearch.WordTrace]
  refine ⟨64345623735615799046495651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42897082490410532697663767 64345623735615799046495651)
  ·
    refine ⟨96518435603423698569743477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64345623735615799046495651 96518435603423698569743477)
    ·
      refine ⟨9048603337820971740913451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96518435603423698569743477 9048603337820971740913451)
      ·
        refine ⟨13572905006731457611370177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9048603337820971740913451 13572905006731457611370177)
        ·
          refine ⟨10179678755048593208527633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13572905006731457611370177 10179678755048593208527633)
          ·
            refine ⟨7634759066286444906395725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10179678755048593208527633 7634759066286444906395725)
            ·
              refine ⟨2863034649857416839898397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7634759066286444906395725 2863034649857416839898397)
              ·
                refine ⟨1073637993696531314961899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2863034649857416839898397 1073637993696531314961899)
                ·
                  refine ⟨1610456990544796972442849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1073637993696531314961899 1610456990544796972442849)
                  ·
                    refine ⟨1207842742908597729332137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1610456990544796972442849 1207842742908597729332137)
                    ·
                      refine ⟨905882057181448296999103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1207842742908597729332137 905882057181448296999103)
                      ·
                        rfl

theorem cell23_1764199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_1764199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764199 prefixEnd_1764199 := by exact prefixLift 1764199
  have htrace : WordTrace (prefixWord ++ tailWord_1764199) baseStart_1764199 baseEnd_1764199 := by
    simpa [prefixWord, tailWord_1764199, baseEnd_1764199] using wordTrace_append hprefix tailTrace_1764199
  have hstable : (prefixWord ++ tailWord_1764199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764199).length < 2 ^ (prefixWord ++ tailWord_1764199).sum := by decide
  have hdescent : baseEnd_1764199 < baseStart_1764199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764232 : List Nat := [2, 1, 3, 3, 2, 2, 1, 3, 2, 1, 3]
def baseStart_1764232 : Nat := 118140960795 + 1764232 * 2 ^ 59
def prefixEnd_1764232 : Nat := 4983230072969 + 3 ^ 40 * 1764232 * 2
def baseEnd_1764232 : Nat := 905899002043046667886451

theorem tailTrace_1764232 : CollatzResearch.WordTrace tailWord_1764232 prefixEnd_1764232 905899002043046667886451 := by
  unfold tailWord_1764232
  simp only [CollatzResearch.WordTrace]
  refine ⟨32173413672248122841223475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42897884896330830454964633 32173413672248122841223475)
  ·
    refine ⟨48260120508372184261835213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32173413672248122841223475 48260120508372184261835213)
    ·
      refine ⟨18097545190639569098188205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48260120508372184261835213 18097545190639569098188205)
      ·
        refine ⟨6786579446489838411820577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18097545190639569098188205 6786579446489838411820577)
        ·
          refine ⟨5089934584867378808865433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6786579446489838411820577 5089934584867378808865433)
          ·
            refine ⟨3817450938650534106649075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5089934584867378808865433 3817450938650534106649075)
            ·
              refine ⟨5726176407975801159973613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3817450938650534106649075 5726176407975801159973613)
              ·
                refine ⟨2147316152990925434990105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5726176407975801159973613 2147316152990925434990105)
                ·
                  refine ⟨1610487114743194076242579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2147316152990925434990105 1610487114743194076242579)
                  ·
                    refine ⟨2415730672114791114363869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1610487114743194076242579 2415730672114791114363869)
                    ·
                      refine ⟨905899002043046667886451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2415730672114791114363869 905899002043046667886451)
                      ·
                        rfl

theorem cell23_1764232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_1764232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764232 prefixEnd_1764232 := by exact prefixLift 1764232
  have htrace : WordTrace (prefixWord ++ tailWord_1764232) baseStart_1764232 baseEnd_1764232 := by
    simpa [prefixWord, tailWord_1764232, baseEnd_1764232] using wordTrace_append hprefix tailTrace_1764232
  have hstable : (prefixWord ++ tailWord_1764232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764232).length < 2 ^ (prefixWord ++ tailWord_1764232).sum := by decide
  have hdescent : baseEnd_1764232 < baseStart_1764232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764255 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 3, 4, 2]
def baseStart_1764255 : Nat := 118140960795 + 1764255 * 2 ^ 59
def prefixEnd_1764255 : Nat := 4983230072969 + 3 ^ 40 * 1764255 * 2
def baseEnd_1764255 : Nat := 905910812098100077898845

theorem tailTrace_1764255 : CollatzResearch.WordTrace tailWord_1764255 prefixEnd_1764255 905910812098100077898845 := by
  unfold tailWord_1764255
  simp only [CollatzResearch.WordTrace]
  refine ⟨64347666223412920610534219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42898444148941947073689479 64347666223412920610534219)
  ·
    refine ⟨96521499335119380915801329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64347666223412920610534219 96521499335119380915801329)
    ·
      refine ⟨72391124501339535686850997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96521499335119380915801329 72391124501339535686850997)
      ·
        refine ⟨6786667922000581470642281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72391124501339535686850997 6786667922000581470642281)
        ·
          refine ⟨5090000941500436102981711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6786667922000581470642281 5090000941500436102981711)
          ·
            refine ⟨7635001412250654154472567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5090000941500436102981711 7635001412250654154472567)
            ·
              refine ⟨11452502118375981231708851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7635001412250654154472567 11452502118375981231708851)
              ·
                refine ⟨17178753177563971847563277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11452502118375981231708851 17178753177563971847563277)
                ·
                  refine ⟨6442032441586489442836229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17178753177563971847563277 6442032441586489442836229)
                  ·
                    refine ⟨1207881082797466770531793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6442032441586489442836229 1207881082797466770531793)
                    ·
                      refine ⟨905910812098100077898845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1207881082797466770531793 905910812098100077898845)
                      ·
                        rfl

theorem cell23_1764255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_1764255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764255 prefixEnd_1764255 := by exact prefixLift 1764255
  have htrace : WordTrace (prefixWord ++ tailWord_1764255) baseStart_1764255 baseEnd_1764255 := by
    simpa [prefixWord, tailWord_1764255, baseEnd_1764255] using wordTrace_append hprefix tailTrace_1764255
  have hstable : (prefixWord ++ tailWord_1764255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764255).length < 2 ^ (prefixWord ++ tailWord_1764255).sum := by decide
  have hdescent : baseEnd_1764255 < baseStart_1764255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764285 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 2, 2, 4]
def baseStart_1764285 : Nat := 118140960795 + 1764285 * 2 ^ 59
def prefixEnd_1764285 : Nat := 4983230072969 + 3 ^ 40 * 1764285 * 2
def baseEnd_1764285 : Nat := 905926216517734960523707

theorem tailTrace_1764285 : CollatzResearch.WordTrace tailWord_1764285 prefixEnd_1764285 905926216517734960523707 := by
  unfold tailWord_1764285
  simp only [CollatzResearch.WordTrace]
  refine ⟨64348760413304235734126309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42899173608869490489417539 64348760413304235734126309)
  ·
    refine ⟨12065392577494544200148683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64348760413304235734126309 12065392577494544200148683)
    ·
      refine ⟨18098088866241816300223025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12065392577494544200148683 18098088866241816300223025)
      ·
        refine ⟨13573566649681362225167269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18098088866241816300223025 13573566649681362225167269)
        ·
          refine ⟨2545043746815255417218863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13573566649681362225167269 2545043746815255417218863)
          ·
            refine ⟨3817565620222883125828295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2545043746815255417218863 3817565620222883125828295)
            ·
              refine ⟨5726348430334324688742443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3817565620222883125828295 5726348430334324688742443)
              ·
                refine ⟨8589522645501487033113665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5726348430334324688742443 8589522645501487033113665)
                ·
                  refine ⟨6442141984126115274835249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8589522645501487033113665 6442141984126115274835249)
                  ·
                    refine ⟨4831606488094586456126437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6442141984126115274835249 4831606488094586456126437)
                    ·
                      refine ⟨905926216517734960523707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4831606488094586456126437 905926216517734960523707)
                      ·
                        rfl

theorem cell23_1764285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_1764285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764285 prefixEnd_1764285 := by exact prefixLift 1764285
  have htrace : WordTrace (prefixWord ++ tailWord_1764285) baseStart_1764285 baseEnd_1764285 := by
    simpa [prefixWord, tailWord_1764285, baseEnd_1764285] using wordTrace_append hprefix tailTrace_1764285
  have hstable : (prefixWord ++ tailWord_1764285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764285).length < 2 ^ (prefixWord ++ tailWord_1764285).sum := by decide
  have hdescent : baseEnd_1764285 < baseStart_1764285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764288 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 3]
def baseStart_1764288 : Nat := 118140960795 + 1764288 * 2 ^ 59
def prefixEnd_1764288 : Nat := 4983230072969 + 3 ^ 40 * 1764288 * 2
def baseEnd_1764288 : Nat := 905927756959698448786193

theorem tailTrace_1764288 : CollatzResearch.WordTrace tailWord_1764288 prefixEnd_1764288 905927756959698448786193 := by
  unfold tailWord_1764288
  simp only [CollatzResearch.WordTrace]
  refine ⟨32174434916146683623242759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42899246554862244830990345 32174434916146683623242759)
  ·
    refine ⟨48261652374220025434864139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32174434916146683623242759 48261652374220025434864139)
    ·
      refine ⟨72392478561330038152296209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48261652374220025434864139 72392478561330038152296209)
      ·
        refine ⟨54294358920997528614222157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72392478561330038152296209 54294358920997528614222157)
        ·
          refine ⟨20360384595374073230333309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54294358920997528614222157 20360384595374073230333309)
          ·
            refine ⟨7635144223265277461374991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20360384595374073230333309 7635144223265277461374991)
            ·
              refine ⟨11452716334897916192062487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7635144223265277461374991 11452716334897916192062487)
              ·
                refine ⟨17179074502346874288093731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11452716334897916192062487 17179074502346874288093731)
                ·
                  refine ⟨25768611753520311432140597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17179074502346874288093731 25768611753520311432140597)
                  ·
                    refine ⟨2415807351892529196763181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25768611753520311432140597 2415807351892529196763181)
                    ·
                      refine ⟨905927756959698448786193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2415807351892529196763181 905927756959698448786193)
                      ·
                        rfl

theorem cell23_1764288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_1764288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764288 prefixEnd_1764288 := by exact prefixLift 1764288
  have htrace : WordTrace (prefixWord ++ tailWord_1764288) baseStart_1764288 baseEnd_1764288 := by
    simpa [prefixWord, tailWord_1764288, baseEnd_1764288] using wordTrace_append hprefix tailTrace_1764288
  have hstable : (prefixWord ++ tailWord_1764288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764288).length < 2 ^ (prefixWord ++ tailWord_1764288).sum := by decide
  have hdescent : baseEnd_1764288 < baseStart_1764288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764291 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 3, 7]
def baseStart_1764291 : Nat := 118140960795 + 1764291 * 2 ^ 59
def prefixEnd_1764291 : Nat := 4983230072969 + 3 ^ 40 * 1764291 * 2
def baseEnd_1764291 : Nat := 301976432467220645682893

theorem tailTrace_1764291 : CollatzResearch.WordTrace tailWord_1764291 prefixEnd_1764291 301976432467220645682893 := by
  unfold tailWord_1764291
  simp only [CollatzResearch.WordTrace]
  refine ⟨64348979251282498758844727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42899319500854999172563151 64348979251282498758844727)
  ·
    refine ⟨96523468876923748138267091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64348979251282498758844727 96523468876923748138267091)
    ·
      refine ⟨144785203315385622207400637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96523468876923748138267091 144785203315385622207400637)
      ·
        refine ⟨54294451243269608327775239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144785203315385622207400637 54294451243269608327775239)
        ·
          refine ⟨81441676864904412491662859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54294451243269608327775239 81441676864904412491662859)
          ·
            refine ⟨122162515297356618737494289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81441676864904412491662859 122162515297356618737494289)
            ·
              refine ⟨91621886473017464053120717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122162515297356618737494289 91621886473017464053120717)
              ·
                refine ⟨34358207427381549019920269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91621886473017464053120717 34358207427381549019920269)
                ·
                  refine ⟨12884327785268080882470101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34358207427381549019920269 12884327785268080882470101)
                  ·
                    refine ⟨301976432467220645682893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12884327785268080882470101 301976432467220645682893)
                    ·
                      rfl

theorem cell23_1764291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 7].length) (baseStart_1764291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764291 prefixEnd_1764291 := by exact prefixLift 1764291
  have htrace : WordTrace (prefixWord ++ tailWord_1764291) baseStart_1764291 baseEnd_1764291 := by
    simpa [prefixWord, tailWord_1764291, baseEnd_1764291] using wordTrace_append hprefix tailTrace_1764291
  have hstable : (prefixWord ++ tailWord_1764291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764291).length < 2 ^ (prefixWord ++ tailWord_1764291).sum := by decide
  have hdescent : baseEnd_1764291 < baseStart_1764291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764322 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_1764322 : Nat := 118140960795 + 1764322 * 2 ^ 59
def prefixEnd_1764322 : Nat := 4983230072969 + 3 ^ 40 * 1764322 * 2
def baseEnd_1764322 : Nat := 905945215301951315761037

theorem tailTrace_1764322 : CollatzResearch.WordTrace tailWord_1764322 prefixEnd_1764322 905945215301951315761037 := by
  unfold tailWord_1764322
  simp only [CollatzResearch.WordTrace]
  refine ⟨16087527478542547763305805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42900073276113460702148813 16087527478542547763305805)
  ·
    refine ⟨6032822804453455411239677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16087527478542547763305805 6032822804453455411239677)
    ·
      refine ⟨2262308551670045779214879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6032822804453455411239677 2262308551670045779214879)
      ·
        refine ⟨3393462827505068668822319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2262308551670045779214879 3393462827505068668822319)
        ·
          refine ⟨5090194241257603003233479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3393462827505068668822319 5090194241257603003233479)
          ·
            refine ⟨7635291361886404504850219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5090194241257603003233479 7635291361886404504850219)
            ·
              refine ⟨11452937042829606757275329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7635291361886404504850219 11452937042829606757275329)
              ·
                refine ⟨8589702782122205067956497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11452937042829606757275329 8589702782122205067956497)
                ·
                  refine ⟨6442277086591653800967373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8589702782122205067956497 6442277086591653800967373)
                  ·
                    refine ⟨2415853907471870175362765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6442277086591653800967373 2415853907471870175362765)
                    ·
                      refine ⟨905945215301951315761037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2415853907471870175362765 905945215301951315761037)
                      ·
                        rfl

theorem cell23_1764322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_1764322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764322 prefixEnd_1764322 := by exact prefixLift 1764322
  have htrace : WordTrace (prefixWord ++ tailWord_1764322) baseStart_1764322 baseEnd_1764322 := by
    simpa [prefixWord, tailWord_1764322, baseEnd_1764322] using wordTrace_append hprefix tailTrace_1764322
  have hstable : (prefixWord ++ tailWord_1764322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764322).length < 2 ^ (prefixWord ++ tailWord_1764322).sum := by decide
  have hdescent : baseEnd_1764322 < baseStart_1764322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764340 : List Nat := [2, 6, 2, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_1764340 : Nat := 118140960795 + 1764340 * 2 ^ 59
def prefixEnd_1764340 : Nat := 4983230072969 + 3 ^ 40 * 1764340 * 2
def baseEnd_1764340 : Nat := 905954457953732245335955

theorem tailTrace_1764340 : CollatzResearch.WordTrace tailWord_1764340 prefixEnd_1764340 905954457953732245335955 := by
  unfold tailWord_1764340
  simp only [CollatzResearch.WordTrace]
  refine ⟨32175383214052490063689237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42900510952069986751585649 32175383214052490063689237)
  ·
    refine ⟨1508221088158710471735433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32175383214052490063689237 1508221088158710471735433)
    ·
      refine ⟨1131165816119032853801575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1508221088158710471735433 1131165816119032853801575)
      ·
        refine ⟨1696748724178549280702363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1131165816119032853801575 1696748724178549280702363)
        ·
          refine ⟨2545123086267823921053545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1696748724178549280702363 2545123086267823921053545)
          ·
            refine ⟨1908842314700867940790159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2545123086267823921053545 1908842314700867940790159)
            ·
              refine ⟨2863263472051301911185239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1908842314700867940790159 2863263472051301911185239)
              ·
                refine ⟨4294895208076952866777859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2863263472051301911185239 4294895208076952866777859)
                ·
                  refine ⟨6442342812115429300166789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4294895208076952866777859 6442342812115429300166789)
                  ·
                    refine ⟨1207939277271642993781273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6442342812115429300166789 1207939277271642993781273)
                    ·
                      refine ⟨905954457953732245335955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1207939277271642993781273 905954457953732245335955)
                      ·
                        rfl

theorem cell23_1764340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_1764340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764340 prefixEnd_1764340 := by exact prefixLift 1764340
  have htrace : WordTrace (prefixWord ++ tailWord_1764340) baseStart_1764340 baseEnd_1764340 := by
    simpa [prefixWord, tailWord_1764340, baseEnd_1764340] using wordTrace_append hprefix tailTrace_1764340
  have hstable : (prefixWord ++ tailWord_1764340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764340).length < 2 ^ (prefixWord ++ tailWord_1764340).sum := by decide
  have hdescent : baseEnd_1764340 < baseStart_1764340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764345 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 2, 4, 2]
def baseStart_1764345 : Nat := 118140960795 + 1764345 * 2 ^ 59
def prefixEnd_1764345 : Nat := 4983230072969 + 3 ^ 40 * 1764345 * 2
def baseEnd_1764345 : Nat := 905957025357004725773431

theorem tailTrace_1764345 : CollatzResearch.WordTrace tailWord_1764345 prefixEnd_1764345 905957025357004725773431 := by
  unfold tailWord_1764345
  simp only [CollatzResearch.WordTrace]
  refine ⟨64350948793086865981310489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42900632528724577320873659 64350948793086865981310489)
  ·
    refine ⟨48263211594815149485982867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64350948793086865981310489 48263211594815149485982867)
    ·
      refine ⟨72394817392222724228974301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48263211594815149485982867 72394817392222724228974301)
      ·
        refine ⟨27148056522083521585865363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72394817392222724228974301 27148056522083521585865363)
        ·
          refine ⟨40722084783125282378798045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27148056522083521585865363 40722084783125282378798045)
          ·
            refine ⟨15270781793671980892049267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40722084783125282378798045 15270781793671980892049267)
            ·
              refine ⟨22906172690507971338073901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15270781793671980892049267 22906172690507971338073901)
              ·
                refine ⟨8589814758940489251777713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22906172690507971338073901 8589814758940489251777713)
                ·
                  refine ⟨6442361069205366938833285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8589814758940489251777713 6442361069205366938833285)
                  ·
                    refine ⟨1207942700476006301031241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6442361069205366938833285 1207942700476006301031241)
                    ·
                      refine ⟨905957025357004725773431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1207942700476006301031241 905957025357004725773431)
                      ·
                        rfl

theorem cell23_1764345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_1764345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764345 prefixEnd_1764345 := by exact prefixLift 1764345
  have htrace : WordTrace (prefixWord ++ tailWord_1764345) baseStart_1764345 baseEnd_1764345 := by
    simpa [prefixWord, tailWord_1764345, baseEnd_1764345] using wordTrace_append hprefix tailTrace_1764345
  have hstable : (prefixWord ++ tailWord_1764345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764345).length < 2 ^ (prefixWord ++ tailWord_1764345).sum := by decide
  have hdescent : baseEnd_1764345 < baseStart_1764345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764389 : List Nat := [1, 3, 1, 2, 2, 2, 5, 2, 1, 4]
def baseStart_1764389 : Nat := 118140960795 + 1764389 * 2 ^ 59
def prefixEnd_1764389 : Nat := 4983230072969 + 3 ^ 40 * 1764389 * 2
def baseEnd_1764389 : Nat := 301993206168600851207743

theorem tailTrace_1764389 : CollatzResearch.WordTrace tailWord_1764389 prefixEnd_1764389 301993206168600851207743 := by
  unfold tailWord_1764389
  simp only [CollatzResearch.WordTrace]
  refine ⟨64352553604927461495912221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42901702403284974330608147 64352553604927461495912221)
  ·
    refine ⟨24132207601847798060967083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64352553604927461495912221 24132207601847798060967083)
    ·
      refine ⟨36198311402771697091450625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24132207601847798060967083 36198311402771697091450625)
      ·
        refine ⟨27148733552078772818587969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36198311402771697091450625 27148733552078772818587969)
        ·
          refine ⟨20361550164059079613940977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27148733552078772818587969 20361550164059079613940977)
          ·
            refine ⟨15271162623044309710455733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20361550164059079613940977 15271162623044309710455733)
            ·
              refine ⟨1431671495910404035355225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15271162623044309710455733 1431671495910404035355225)
              ·
                refine ⟨1073753621932803026516419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1431671495910404035355225 1073753621932803026516419)
                ·
                  refine ⟨1610630432899204539774629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1073753621932803026516419 1610630432899204539774629)
                  ·
                    refine ⟨301993206168600851207743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1610630432899204539774629 301993206168600851207743)
                    ·
                      rfl

theorem cell23_1764389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 1, 4].length) (baseStart_1764389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764389 prefixEnd_1764389 := by exact prefixLift 1764389
  have htrace : WordTrace (prefixWord ++ tailWord_1764389) baseStart_1764389 baseEnd_1764389 := by
    simpa [prefixWord, tailWord_1764389, baseEnd_1764389] using wordTrace_append hprefix tailTrace_1764389
  have hstable : (prefixWord ++ tailWord_1764389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764389).length < 2 ^ (prefixWord ++ tailWord_1764389).sum := by decide
  have hdescent : baseEnd_1764389 < baseStart_1764389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764462 : List Nat := [4, 1, 2, 2, 1, 3, 2, 1, 1, 6]
def baseStart_1764462 : Nat := 118140960795 + 1764462 * 2 ^ 59
def prefixEnd_1764462 : Nat := 4983230072969 + 3 ^ 40 * 1764462 * 2
def baseEnd_1764462 : Nat := 302005700864526922670131

theorem tailTrace_1764462 : CollatzResearch.WordTrace tailWord_1764462 prefixEnd_1764462 302005700864526922670131 := by
  unfold tailWord_1764462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8044402016707874370414955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42903477422441996642213093 8044402016707874370414955)
  ·
    refine ⟨12066603025061811555622433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8044402016707874370414955 12066603025061811555622433)
    ·
      refine ⟨9049952268796358666716825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12066603025061811555622433 9049952268796358666716825)
      ·
        refine ⟨6787464201597269000037619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9049952268796358666716825 6787464201597269000037619)
        ·
          refine ⟨10181196302395903500056429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6787464201597269000037619 10181196302395903500056429)
          ·
            refine ⟨3817948613398463812521161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10181196302395903500056429 3817948613398463812521161)
            ·
              refine ⟨2863461460048847859390871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3817948613398463812521161 2863461460048847859390871)
              ·
                refine ⟨4295192190073271789086307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2863461460048847859390871 4295192190073271789086307)
                ·
                  refine ⟨6442788285109907683629461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4295192190073271789086307 6442788285109907683629461)
                  ·
                    refine ⟨302005700864526922670131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6442788285109907683629461 302005700864526922670131)
                    ·
                      rfl

theorem cell23_1764462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_1764462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764462 prefixEnd_1764462 := by exact prefixLift 1764462
  have htrace : WordTrace (prefixWord ++ tailWord_1764462) baseStart_1764462 baseEnd_1764462 := by
    simpa [prefixWord, tailWord_1764462, baseEnd_1764462] using wordTrace_append hprefix tailTrace_1764462
  have hstable : (prefixWord ++ tailWord_1764462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764462).length < 2 ^ (prefixWord ++ tailWord_1764462).sum := by decide
  have hdescent : baseEnd_1764462 < baseStart_1764462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764489 : List Nat := [1, 2, 1, 1, 4, 3, 4, 1, 1, 2, 3]
def baseStart_1764489 : Nat := 118140960795 + 1764489 * 2 ^ 59
def prefixEnd_1764489 : Nat := 4983230072969 + 3 ^ 40 * 1764489 * 2
def baseEnd_1764489 : Nat := 906030966571252162372769

theorem tailTrace_1764489 : CollatzResearch.WordTrace tailWord_1764489 prefixEnd_1764489 906030966571252162372769 := by
  unfold tailWord_1764489
  simp only [CollatzResearch.WordTrace]
  refine ⟨64356200904565178574552521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42904133936376785716368347 64356200904565178574552521)
  ·
    refine ⟨48267150678423883930914391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64356200904565178574552521 48267150678423883930914391)
    ·
      refine ⟨72400726017635825896371587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48267150678423883930914391 72400726017635825896371587)
      ·
        refine ⟨108601089026453738844557381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72400726017635825896371587 108601089026453738844557381)
        ·
          refine ⟨20362704192460076033354509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108601089026453738844557381 20362704192460076033354509)
          ·
            refine ⟨7636014072172528512507941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20362704192460076033354509 7636014072172528512507941)
            ·
              refine ⟨1431752638532349096095239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7636014072172528512507941 1431752638532349096095239)
              ·
                refine ⟨2147628957798523644142859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1431752638532349096095239 2147628957798523644142859)
                ·
                  refine ⟨3221443436697785466214289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2147628957798523644142859 3221443436697785466214289)
                  ·
                    refine ⟨2416082577523339099660717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3221443436697785466214289 2416082577523339099660717)
                    ·
                      refine ⟨906030966571252162372769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2416082577523339099660717 906030966571252162372769)
                      ·
                        rfl

theorem cell23_1764489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 1, 2, 3].length) (baseStart_1764489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764489 prefixEnd_1764489 := by exact prefixLift 1764489
  have htrace : WordTrace (prefixWord ++ tailWord_1764489) baseStart_1764489 baseEnd_1764489 := by
    simpa [prefixWord, tailWord_1764489, baseEnd_1764489] using wordTrace_append hprefix tailTrace_1764489
  have hstable : (prefixWord ++ tailWord_1764489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764489).length < 2 ^ (prefixWord ++ tailWord_1764489).sum := by decide
  have hdescent : baseEnd_1764489 < baseStart_1764489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764519 : List Nat := [1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_1764519 : Nat := 118140960795 + 1764519 * 2 ^ 59
def prefixEnd_1764519 : Nat := 4983230072969 + 3 ^ 40 * 1764519 * 2
def baseEnd_1764519 : Nat := 906046370990887044997631

theorem tailTrace_1764519 : CollatzResearch.WordTrace tailWord_1764519 prefixEnd_1764519 906046370990887044997631 := by
  unfold tailWord_1764519
  simp only [CollatzResearch.WordTrace]
  refine ⟨64357295094456493698144611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42904863396304329132096407 64357295094456493698144611)
  ·
    refine ⟨96535942641684740547216917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64357295094456493698144611 96535942641684740547216917)
    ·
      refine ⟨4525122311328972213150793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 96535942641684740547216917 4525122311328972213150793)
      ·
        refine ⟨3393841733496729159863095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4525122311328972213150793 3393841733496729159863095)
        ·
          refine ⟨5090762600245093739794643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3393841733496729159863095 5090762600245093739794643)
          ·
            refine ⟨7636143900367640609691965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5090762600245093739794643 7636143900367640609691965)
            ·
              refine ⟨2863553962637865228634487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7636143900367640609691965 2863553962637865228634487)
              ·
                refine ⟨4295330943956797842951731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2863553962637865228634487 4295330943956797842951731)
                ·
                  refine ⟨6442996415935196764427597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4295330943956797842951731 6442996415935196764427597)
                  ·
                    refine ⟨2416123655975698786660349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6442996415935196764427597 2416123655975698786660349)
                    ·
                      refine ⟨906046370990887044997631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2416123655975698786660349 906046370990887044997631)
                      ·
                        rfl

theorem cell23_1764519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_1764519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764519 prefixEnd_1764519 := by exact prefixLift 1764519
  have htrace : WordTrace (prefixWord ++ tailWord_1764519) baseStart_1764519 baseEnd_1764519 := by
    simpa [prefixWord, tailWord_1764519, baseEnd_1764519] using wordTrace_append hprefix tailTrace_1764519
  have hstable : (prefixWord ++ tailWord_1764519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764519).length < 2 ^ (prefixWord ++ tailWord_1764519).sum := by decide
  have hdescent : baseEnd_1764519 < baseStart_1764519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764555 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 4]
def baseStart_1764555 : Nat := 118140960795 + 1764555 * 2 ^ 59
def prefixEnd_1764555 : Nat := 4983230072969 + 3 ^ 40 * 1764555 * 2
def baseEnd_1764555 : Nat := 906064856294448904147465

theorem tailTrace_1764555 : CollatzResearch.WordTrace tailWord_1764555 prefixEnd_1764555 906064856294448904147465 := by
  unfold tailWord_1764555
  simp only [CollatzResearch.WordTrace]
  refine ⟨64358608122326071846455119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42905738748217381230970079 64358608122326071846455119)
  ·
    refine ⟨96537912183489107769682679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64358608122326071846455119 96537912183489107769682679)
    ·
      refine ⟨144806868275233661654524019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96537912183489107769682679 144806868275233661654524019)
      ·
        refine ⟨217210302412850492481786029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144806868275233661654524019 217210302412850492481786029)
        ·
          refine ⟨81453863404818934680669761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217210302412850492481786029 81453863404818934680669761)
          ·
            refine ⟨61090397553614201010502321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81453863404818934680669761 61090397553614201010502321)
            ·
              refine ⟨45817798165210650757876741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61090397553614201010502321 45817798165210650757876741)
              ·
                refine ⟨8590837155976997017101889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45817798165210650757876741 8590837155976997017101889)
                ·
                  refine ⟨6443127866982747762826417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8590837155976997017101889 6443127866982747762826417)
                  ·
                    refine ⟨4832345900237060822119813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6443127866982747762826417 4832345900237060822119813)
                    ·
                      refine ⟨906064856294448904147465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4832345900237060822119813 906064856294448904147465)
                      ·
                        rfl

theorem cell23_1764555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 4].length) (baseStart_1764555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764555 prefixEnd_1764555 := by exact prefixLift 1764555
  have htrace : WordTrace (prefixWord ++ tailWord_1764555) baseStart_1764555 baseEnd_1764555 := by
    simpa [prefixWord, tailWord_1764555, baseEnd_1764555] using wordTrace_append hprefix tailTrace_1764555
  have hstable : (prefixWord ++ tailWord_1764555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764555).length < 2 ^ (prefixWord ++ tailWord_1764555).sum := by decide
  have hdescent : baseEnd_1764555 < baseStart_1764555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764562 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_1764562 : Nat := 118140960795 + 1764562 * 2 ^ 59
def prefixEnd_1764562 : Nat := 4983230072969 + 3 ^ 40 * 1764562 * 2
def baseEnd_1764562 : Nat := 906068450659030376759933

theorem tailTrace_1764562 : CollatzResearch.WordTrace tailWord_1764562 prefixEnd_1764562 906068450659030376759933 := by
  unfold tailWord_1764562
  simp only [CollatzResearch.WordTrace]
  refine ⟨16089715858325178010489985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42905908955533808027973293 16089715858325178010489985)
  ·
    refine ⟨12067286893743883507867489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16089715858325178010489985 12067286893743883507867489)
    ·
      refine ⟨9050465170307912630900617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12067286893743883507867489 9050465170307912630900617)
      ·
        refine ⟨6787848877730934473175463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9050465170307912630900617 6787848877730934473175463)
        ·
          refine ⟨10181773316596401709763195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6787848877730934473175463 10181773316596401709763195)
          ·
            refine ⟨15272659974894602564644793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10181773316596401709763195 15272659974894602564644793)
            ·
              refine ⟨11454494981170951923483595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15272659974894602564644793 11454494981170951923483595)
              ·
                refine ⟨17181742471756427885225393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11454494981170951923483595 17181742471756427885225393)
                ·
                  refine ⟨12886306853817320913919045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17181742471756427885225393 12886306853817320913919045)
                  ·
                    refine ⟨2416182535090747671359821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12886306853817320913919045 2416182535090747671359821)
                    ·
                      refine ⟨906068450659030376759933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2416182535090747671359821 906068450659030376759933)
                      ·
                        rfl

theorem cell23_1764562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_1764562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764562 prefixEnd_1764562 := by exact prefixLift 1764562
  have htrace : WordTrace (prefixWord ++ tailWord_1764562) baseStart_1764562 baseEnd_1764562 := by
    simpa [prefixWord, tailWord_1764562, baseEnd_1764562] using wordTrace_append hprefix tailTrace_1764562
  have hstable : (prefixWord ++ tailWord_1764562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764562).length < 2 ^ (prefixWord ++ tailWord_1764562).sum := by decide
  have hdescent : baseEnd_1764562 < baseStart_1764562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764576 : List Nat := [2, 1, 1, 3, 1, 5, 1, 3, 2, 2, 2]
def baseStart_1764576 : Nat := 118140960795 + 1764576 * 2 ^ 59
def prefixEnd_1764576 : Nat := 4983230072969 + 3 ^ 40 * 1764576 * 2
def baseEnd_1764576 : Nat := 906075639388193321984869

theorem tailTrace_1764576 : CollatzResearch.WordTrace tailWord_1764576 prefixEnd_1764576 906075639388193321984869 := by
  unfold tailWord_1764576
  simp only [CollatzResearch.WordTrace]
  refine ⟨32179687027624996216484791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42906249370166661621979721 32179687027624996216484791)
  ·
    refine ⟨48269530541437494324727187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32179687027624996216484791 48269530541437494324727187)
    ·
      refine ⟨72404295812156241487090781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48269530541437494324727187 72404295812156241487090781)
      ·
        refine ⟨27151610929558590557659043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72404295812156241487090781 27151610929558590557659043)
        ·
          refine ⟨40727416394337885836488565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27151610929558590557659043 40727416394337885836488565)
          ·
            refine ⟨3818195286969176797170803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40727416394337885836488565 3818195286969176797170803)
            ·
              refine ⟨5727292930453765195756205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3818195286969176797170803 5727292930453765195756205)
              ·
                refine ⟨2147734848920161948408577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5727292930453765195756205 2147734848920161948408577)
                ·
                  refine ⟨1610801136690121461306433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2147734848920161948408577 1610801136690121461306433)
                  ·
                    refine ⟨1208100852517591095979825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1610801136690121461306433 1208100852517591095979825)
                    ·
                      refine ⟨906075639388193321984869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1208100852517591095979825 906075639388193321984869)
                      ·
                        rfl

theorem cell23_1764576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_1764576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764576 prefixEnd_1764576 := by exact prefixLift 1764576
  have htrace : WordTrace (prefixWord ++ tailWord_1764576) baseStart_1764576 baseEnd_1764576 := by
    simpa [prefixWord, tailWord_1764576, baseEnd_1764576] using wordTrace_append hprefix tailTrace_1764576
  have hstable : (prefixWord ++ tailWord_1764576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764576).length < 2 ^ (prefixWord ++ tailWord_1764576).sum := by decide
  have hdescent : baseEnd_1764576 < baseStart_1764576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764610 : List Nat := [3, 4, 1, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_1764610 : Nat := 118140960795 + 1764610 * 2 ^ 59
def prefixEnd_1764610 : Nat := 4983230072969 + 3 ^ 40 * 1764610 * 2
def baseEnd_1764610 : Nat := 906093097730446188959713

theorem tailTrace_1764610 : CollatzResearch.WordTrace tailWord_1764610 prefixEnd_1764610 906093097730446188959713 := by
  unfold tailWord_1764610
  simp only [CollatzResearch.WordTrace]
  refine ⟨16090153534281704059926821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42907076091417877493138189 16090153534281704059926821)
  ·
    refine ⟨3016903787677819511236279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16090153534281704059926821 3016903787677819511236279)
    ·
      refine ⟨4525355681516729266854419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3016903787677819511236279 4525355681516729266854419)
      ·
        refine ⟨6788033522275093900281629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4525355681516729266854419 6788033522275093900281629)
        ·
          refine ⟨2545512570853160212605611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6788033522275093900281629 2545512570853160212605611)
          ·
            refine ⟨3818268856279740318908417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2545512570853160212605611 3818268856279740318908417)
            ·
              refine ⟨2863701642209805239181313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3818268856279740318908417 2863701642209805239181313)
              ·
                refine ⟨2147776231657353929385985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2863701642209805239181313 2147776231657353929385985)
                ·
                  refine ⟨1610832173743015447039489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2147776231657353929385985 1610832173743015447039489)
                  ·
                    refine ⟨1208124130307261585279617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1610832173743015447039489 1208124130307261585279617)
                    ·
                      refine ⟨906093097730446188959713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1208124130307261585279617 906093097730446188959713)
                      ·
                        rfl

theorem cell23_1764610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_1764610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764610 prefixEnd_1764610 := by exact prefixLift 1764610
  have htrace : WordTrace (prefixWord ++ tailWord_1764610) baseStart_1764610 baseEnd_1764610 := by
    simpa [prefixWord, tailWord_1764610, baseEnd_1764610] using wordTrace_append hprefix tailTrace_1764610
  have hstable : (prefixWord ++ tailWord_1764610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764610).length < 2 ^ (prefixWord ++ tailWord_1764610).sum := by decide
  have hdescent : baseEnd_1764610 < baseStart_1764610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764622 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_1764622 : Nat := 118140960795 + 1764622 * 2 ^ 59
def prefixEnd_1764622 : Nat := 4983230072969 + 3 ^ 40 * 1764622 * 2
def baseEnd_1764622 : Nat := 906099259498300142009657

theorem tailTrace_1764622 : CollatzResearch.WordTrace tailWord_1764622 prefixEnd_1764622 906099259498300142009657 := by
  unfold tailWord_1764622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8045131476635417786143015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42907367875388894859429413 8045131476635417786143015)
  ·
    refine ⟨12067697214953126679214523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8045131476635417786143015 12067697214953126679214523)
    ·
      refine ⟨18101545822429690018821785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12067697214953126679214523 18101545822429690018821785)
      ·
        refine ⟨13576159366822267514116339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18101545822429690018821785 13576159366822267514116339)
        ·
          refine ⟨20364239050233401271174509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13576159366822267514116339 20364239050233401271174509)
          ·
            refine ⟨7636589643837525476690441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20364239050233401271174509 7636589643837525476690441)
            ·
              refine ⟨5727442232878144107517831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7636589643837525476690441 5727442232878144107517831)
              ·
                refine ⟨8591163349317216161276747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5727442232878144107517831 8591163349317216161276747)
                ·
                  refine ⟨12886745023975824241915121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8591163349317216161276747 12886745023975824241915121)
                  ·
                    refine ⟨9665058767981868181436341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12886745023975824241915121 9665058767981868181436341)
                    ·
                      refine ⟨906099259498300142009657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9665058767981868181436341 906099259498300142009657)
                      ·
                        rfl

theorem cell23_1764622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_1764622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764622 prefixEnd_1764622 := by exact prefixLift 1764622
  have htrace : WordTrace (prefixWord ++ tailWord_1764622) baseStart_1764622 baseEnd_1764622 := by
    simpa [prefixWord, tailWord_1764622, baseEnd_1764622] using wordTrace_append hprefix tailTrace_1764622
  have hstable : (prefixWord ++ tailWord_1764622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764622).length < 2 ^ (prefixWord ++ tailWord_1764622).sum := by decide
  have hdescent : baseEnd_1764622 < baseStart_1764622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764655 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 8]
def baseStart_1764655 : Nat := 118140960795 + 1764655 * 2 ^ 59
def prefixEnd_1764655 : Nat := 4983230072969 + 3 ^ 40 * 1764655 * 2
def baseEnd_1764655 : Nat := 100679578262210945877445

theorem tailTrace_1764655 : CollatzResearch.WordTrace tailWord_1764655 prefixEnd_1764655 100679578262210945877445 := by
  unfold tailWord_1764655
  simp only [CollatzResearch.WordTrace]
  refine ⟨64362255421963788925095419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42908170281309192616730279 64362255421963788925095419)
  ·
    refine ⟨96543383132945683387643129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64362255421963788925095419 96543383132945683387643129)
    ·
      refine ⟨72407537349709262540732347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96543383132945683387643129 72407537349709262540732347)
      ·
        refine ⟨108611306024563893811098521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72407537349709262540732347 108611306024563893811098521)
        ·
          refine ⟨81458479518422920358323891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108611306024563893811098521 81458479518422920358323891)
          ·
            refine ⟨122187719277634380537485837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81458479518422920358323891 122187719277634380537485837)
            ·
              refine ⟨45820394729112892701557189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122187719277634380537485837 45820394729112892701557189)
              ·
                refine ⟨8591324011708667381541973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45820394729112892701557189 8591324011708667381541973)
                ·
                  refine ⟨100679578262210945877445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8591324011708667381541973 100679578262210945877445)
                  ·
                    rfl

theorem cell23_1764655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 8].length) (baseStart_1764655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764655 prefixEnd_1764655 := by exact prefixLift 1764655
  have htrace : WordTrace (prefixWord ++ tailWord_1764655) baseStart_1764655 baseEnd_1764655 := by
    simpa [prefixWord, tailWord_1764655, baseEnd_1764655] using wordTrace_append hprefix tailTrace_1764655
  have hstable : (prefixWord ++ tailWord_1764655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764655).length < 2 ^ (prefixWord ++ tailWord_1764655).sum := by decide
  have hdescent : baseEnd_1764655 < baseStart_1764655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764676 : List Nat := [2, 3, 4, 1, 1, 1, 1, 3, 3, 4]
def baseStart_1764676 : Nat := 118140960795 + 1764676 * 2 ^ 59
def prefixEnd_1764676 : Nat := 4983230072969 + 3 ^ 40 * 1764676 * 2
def baseEnd_1764676 : Nat := 302042329151214310244803

theorem tailTrace_1764676 : CollatzResearch.WordTrace tailWord_1764676 prefixEnd_1764676 302042329151214310244803 := by
  unfold tailWord_1764676
  simp only [CollatzResearch.WordTrace]
  refine ⟨32181510677443854755804941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42908680903258473007739921 32181510677443854755804941)
  ·
    refine ⟨12068066504041445533426853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32181510677443854755804941 12068066504041445533426853)
    ·
      refine ⟨2262762469507771037517535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12068066504041445533426853 2262762469507771037517535)
      ·
        refine ⟨3394143704261656556276303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2262762469507771037517535 3394143704261656556276303)
        ·
          refine ⟨5091215556392484834414455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3394143704261656556276303 5091215556392484834414455)
          ·
            refine ⟨7636823334588727251621683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5091215556392484834414455 7636823334588727251621683)
            ·
              refine ⟨11455235001883090877432525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7636823334588727251621683 11455235001883090877432525)
              ·
                refine ⟨4295713125706159079037197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11455235001883090877432525 4295713125706159079037197)
                ·
                  refine ⟨1610892422139809654638949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4295713125706159079037197 1610892422139809654638949)
                  ·
                    refine ⟨302042329151214310244803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1610892422139809654638949 302042329151214310244803)
                    ·
                      rfl

theorem cell23_1764676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_1764676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764676 prefixEnd_1764676 := by exact prefixLift 1764676
  have htrace : WordTrace (prefixWord ++ tailWord_1764676) baseStart_1764676 baseEnd_1764676 := by
    simpa [prefixWord, tailWord_1764676, baseEnd_1764676] using wordTrace_append hprefix tailTrace_1764676
  have hstable : (prefixWord ++ tailWord_1764676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764676).length < 2 ^ (prefixWord ++ tailWord_1764676).sum := by decide
  have hdescent : baseEnd_1764676 < baseStart_1764676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764689 : List Nat := [1, 2, 2, 1, 4, 1, 5, 1, 6]
def baseStart_1764689 : Nat := 118140960795 + 1764689 * 2 ^ 59
def prefixEnd_1764689 : Nat := 4983230072969 + 3 ^ 40 * 1764689 * 2
def baseEnd_1764689 : Nat := 100681518078016819985761

theorem tailTrace_1764689 : CollatzResearch.WordTrace tailWord_1764689 prefixEnd_1764689 100681518078016819985761 := by
  unfold tailWord_1764689
  simp only [CollatzResearch.WordTrace]
  refine ⟨64363495503840612731833121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42908997002560408487888747 64363495503840612731833121)
  ·
    refine ⟨48272621627880459548874841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64363495503840612731833121 48272621627880459548874841)
    ·
      refine ⟨36204466220910344661656131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48272621627880459548874841 36204466220910344661656131)
      ·
        refine ⟨54306699331365516992484197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36204466220910344661656131 54306699331365516992484197)
        ·
          refine ⟨10182506124631034436090787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54306699331365516992484197 10182506124631034436090787)
          ·
            refine ⟨15273759186946551654136181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10182506124631034436090787 15273759186946551654136181)
            ·
              refine ⟨1431914923776239217575267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15273759186946551654136181 1431914923776239217575267)
              ·
                refine ⟨2147872385664358826362901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1431914923776239217575267 2147872385664358826362901)
                ·
                  refine ⟨100681518078016819985761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2147872385664358826362901 100681518078016819985761)
                  ·
                    rfl

theorem cell23_1764689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 6].length) (baseStart_1764689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764689 prefixEnd_1764689 := by exact prefixLift 1764689
  have htrace : WordTrace (prefixWord ++ tailWord_1764689) baseStart_1764689 baseEnd_1764689 := by
    simpa [prefixWord, tailWord_1764689, baseEnd_1764689] using wordTrace_append hprefix tailTrace_1764689
  have hstable : (prefixWord ++ tailWord_1764689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764689).length < 2 ^ (prefixWord ++ tailWord_1764689).sum := by decide
  have hdescent : baseEnd_1764689 < baseStart_1764689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764692 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_1764692 : Nat := 118140960795 + 1764692 * 2 ^ 59
def prefixEnd_1764692 : Nat := 4983230072969 + 3 ^ 40 * 1764692 * 2
def baseEnd_1764692 : Nat := 906135203144114868134335

theorem tailTrace_1764692 : CollatzResearch.WordTrace tailWord_1764692 prefixEnd_1764692 906135203144114868134335 := by
  unfold tailWord_1764692
  simp only [CollatzResearch.WordTrace]
  refine ⟨32181802461414872122096165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42909069948553162829461553 32181802461414872122096165)
  ·
    refine ⟨6034087961515288522893031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32181802461414872122096165 6034087961515288522893031)
    ·
      refine ⟨9051131942272932784339547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6034087961515288522893031 9051131942272932784339547)
      ·
        refine ⟨13576697913409399176509321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9051131942272932784339547 13576697913409399176509321)
        ·
          refine ⟨10182523435057049382381991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13576697913409399176509321 10182523435057049382381991)
          ·
            refine ⟨15273785152585574073572987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10182523435057049382381991 15273785152585574073572987)
            ·
              refine ⟨22910677728878361110359481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15273785152585574073572987 22910677728878361110359481)
              ·
                refine ⟨17183008296658770832769611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22910677728878361110359481 17183008296658770832769611)
                ·
                  refine ⟨25774512444988156249154417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17183008296658770832769611 25774512444988156249154417)
                  ·
                    refine ⟨19330884333741117186865813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25774512444988156249154417 19330884333741117186865813)
                    ·
                      refine ⟨906135203144114868134335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19330884333741117186865813 906135203144114868134335)
                      ·
                        rfl

theorem cell23_1764692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_1764692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764692 prefixEnd_1764692 := by exact prefixLift 1764692
  have htrace : WordTrace (prefixWord ++ tailWord_1764692) baseStart_1764692 baseEnd_1764692 := by
    simpa [prefixWord, tailWord_1764692, baseEnd_1764692] using wordTrace_append hprefix tailTrace_1764692
  have hstable : (prefixWord ++ tailWord_1764692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764692).length < 2 ^ (prefixWord ++ tailWord_1764692).sum := by decide
  have hdescent : baseEnd_1764692 < baseStart_1764692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764709 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 1, 5, 2]
def baseStart_1764709 : Nat := 118140960795 + 1764709 * 2 ^ 59
def prefixEnd_1764709 : Nat := 4983230072969 + 3 ^ 40 * 1764709 * 2
def baseEnd_1764709 : Nat := 906143932315241301621757

theorem tailTrace_1764709 : CollatzResearch.WordTrace tailWord_1764709 prefixEnd_1764709 906143932315241301621757 := by
  unfold tailWord_1764709
  simp only [CollatzResearch.WordTrace]
  refine ⟨64364224963768156147561181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42909483309178770765040787 64364224963768156147561181)
  ·
    refine ⟨24136584361413058555335443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64364224963768156147561181 24136584361413058555335443)
    ·
      refine ⟨36204876542119587833003165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24136584361413058555335443 36204876542119587833003165)
      ·
        refine ⟨13576828703294845437376187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36204876542119587833003165 13576828703294845437376187)
        ·
          refine ⟨20365243054942268156064281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13576828703294845437376187 20365243054942268156064281)
          ·
            refine ⟨15273932291206701117048211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20365243054942268156064281 15273932291206701117048211)
            ·
              refine ⟨22910898436810051675572317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15273932291206701117048211 22910898436810051675572317)
              ·
                refine ⟨8591586913803769378339619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22910898436810051675572317 8591586913803769378339619)
                ·
                  refine ⟨12887380370705654067509429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8591586913803769378339619 12887380370705654067509429)
                  ·
                    refine ⟨1208191909753655068829009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12887380370705654067509429 1208191909753655068829009)
                    ·
                      refine ⟨906143932315241301621757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1208191909753655068829009 906143932315241301621757)
                      ·
                        rfl

theorem cell23_1764709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_1764709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764709 prefixEnd_1764709 := by exact prefixLift 1764709
  have htrace : WordTrace (prefixWord ++ tailWord_1764709) baseStart_1764709 baseEnd_1764709 := by
    simpa [prefixWord, tailWord_1764709, baseEnd_1764709] using wordTrace_append hprefix tailTrace_1764709
  have hstable : (prefixWord ++ tailWord_1764709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764709).length < 2 ^ (prefixWord ++ tailWord_1764709).sum := by decide
  have hdescent : baseEnd_1764709 < baseStart_1764709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764756 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_1764756 : Nat := 118140960795 + 1764756 * 2 ^ 59
def prefixEnd_1764756 : Nat := 4983230072969 + 3 ^ 40 * 1764756 * 2
def baseEnd_1764756 : Nat := 906168065906002617734041

theorem tailTrace_1764756 : CollatzResearch.WordTrace tailWord_1764756 prefixEnd_1764756 906168065906002617734041 := by
  unfold tailWord_1764756
  simp only [CollatzResearch.WordTrace]
  refine ⟨32182969597298941587261061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42910626129731922116348081 32182969597298941587261061)
  ·
    refine ⟨6034306799493551547611449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32182969597298941587261061 6034306799493551547611449)
    ·
      refine ⟨4525730099620163660708587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6034306799493551547611449 4525730099620163660708587)
      ·
        refine ⟨6788595149430245491062881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4525730099620163660708587 6788595149430245491062881)
        ·
          refine ⟨5091446362072684118297161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6788595149430245491062881 5091446362072684118297161)
          ·
            refine ⟨3818584771554513088722871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5091446362072684118297161 3818584771554513088722871)
            ·
              refine ⟨5727877157331769633084307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3818584771554513088722871 5727877157331769633084307)
              ·
                refine ⟨8591815735997654449626461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5727877157331769633084307 8591815735997654449626461)
                ·
                  refine ⟨3221930900999120418609923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8591815735997654449626461 3221930900999120418609923)
                  ·
                    refine ⟨4832896351498680627914885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3221930900999120418609923 4832896351498680627914885)
                    ·
                      refine ⟨906168065906002617734041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4832896351498680627914885 906168065906002617734041)
                      ·
                        rfl

theorem cell23_1764756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_1764756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764756 prefixEnd_1764756 := by exact prefixLift 1764756
  have htrace : WordTrace (prefixWord ++ tailWord_1764756) baseStart_1764756 baseEnd_1764756 := by
    simpa [prefixWord, tailWord_1764756, baseEnd_1764756] using wordTrace_append hprefix tailTrace_1764756
  have hstable : (prefixWord ++ tailWord_1764756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764756).length < 2 ^ (prefixWord ++ tailWord_1764756).sum := by decide
  have hdescent : baseEnd_1764756 < baseStart_1764756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764762 : List Nat := [3, 1, 1, 4, 1, 1, 1, 11]
def baseStart_1764762 : Nat := 118140960795 + 1764762 * 2 ^ 59
def prefixEnd_1764762 : Nat := 4983230072969 + 3 ^ 40 * 1764762 * 2
def baseEnd_1764762 : Nat := 33561894325552947935519

theorem tailTrace_1764762 : CollatzResearch.WordTrace tailWord_1764762 prefixEnd_1764762 33561894325552947935519 := by
  unfold tailWord_1764762
  simp only [CollatzResearch.WordTrace]
  refine ⟨16091539508144036549810135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42910772021717430799493693 16091539508144036549810135)
  ·
    refine ⟨24137309262216054824715203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16091539508144036549810135 24137309262216054824715203)
    ·
      refine ⟨36205963893324082237072805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24137309262216054824715203 36205963893324082237072805)
      ·
        refine ⟨6788618229998265419451151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36205963893324082237072805 6788618229998265419451151)
        ·
          refine ⟨10182927344997398129176727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6788618229998265419451151 10182927344997398129176727)
          ·
            refine ⟨15274391017496097193765091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10182927344997398129176727 15274391017496097193765091)
            ·
              refine ⟨22911586526244145790647637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15274391017496097193765091 22911586526244145790647637)
              ·
                refine ⟨33561894325552947935519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 22911586526244145790647637 33561894325552947935519)
                ·
                  rfl

theorem cell23_1764762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 11].length) (baseStart_1764762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764762 prefixEnd_1764762 := by exact prefixLift 1764762
  have htrace : WordTrace (prefixWord ++ tailWord_1764762) baseStart_1764762 baseEnd_1764762 := by
    simpa [prefixWord, tailWord_1764762, baseEnd_1764762] using wordTrace_append hprefix tailTrace_1764762
  have hstable : (prefixWord ++ tailWord_1764762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764762).length < 2 ^ (prefixWord ++ tailWord_1764762).sum := by decide
  have hdescent : baseEnd_1764762 < baseStart_1764762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764792 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 2, 7]
def baseStart_1764792 : Nat := 118140960795 + 1764792 * 2 ^ 59
def prefixEnd_1764792 : Nat := 4983230072969 + 3 ^ 40 * 1764792 * 2
def baseEnd_1764792 : Nat := 302062183736521492294625

theorem tailTrace_1764792 : CollatzResearch.WordTrace tailWord_1764792 prefixEnd_1764792 302062183736521492294625 := by
  unfold tailWord_1764792
  simp only [CollatzResearch.WordTrace]
  refine ⟨32183626111233730661416315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42911501481644974215221753 32183626111233730661416315)
  ·
    refine ⟨48275439166850595992124473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32183626111233730661416315 48275439166850595992124473)
    ·
      refine ⟨36206579375137946994093355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48275439166850595992124473 36206579375137946994093355)
      ·
        refine ⟨54309869062706920491140033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36206579375137946994093355 54309869062706920491140033)
        ·
          refine ⟨40732401797030190368355025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54309869062706920491140033 40732401797030190368355025)
          ·
            refine ⟨30549301347772642776266269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40732401797030190368355025 30549301347772642776266269)
            ·
              refine ⟨11455988005414741041099851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30549301347772642776266269 11455988005414741041099851)
              ·
                refine ⟨17183982008122111561649777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11455988005414741041099851 17183982008122111561649777)
                ·
                  refine ⟨12887986506091583671237333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17183982008122111561649777 12887986506091583671237333)
                  ·
                    refine ⟨302062183736521492294625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12887986506091583671237333 302062183736521492294625)
                    ·
                      rfl

theorem cell23_1764792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_1764792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764792 prefixEnd_1764792 := by exact prefixLift 1764792
  have htrace : WordTrace (prefixWord ++ tailWord_1764792) baseStart_1764792 baseEnd_1764792 := by
    simpa [prefixWord, tailWord_1764792, baseEnd_1764792] using wordTrace_append hprefix tailTrace_1764792
  have hstable : (prefixWord ++ tailWord_1764792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764792).length < 2 ^ (prefixWord ++ tailWord_1764792).sum := by decide
  have hdescent : baseEnd_1764792 < baseStart_1764792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764796 : List Nat := [2, 2, 2, 4, 2, 2, 1, 8]
def baseStart_1764796 : Nat := 118140960795 + 1764796 * 2 ^ 59
def prefixEnd_1764796 : Nat := 4983230072969 + 3 ^ 40 * 1764796 * 2
def baseEnd_1764796 : Nat := 33562540930821572638291

theorem tailTrace_1764796 : CollatzResearch.WordTrace tailWord_1764796 prefixEnd_1764796 33562540930821572638291 := by
  unfold tailWord_1764796
  simp only [CollatzResearch.WordTrace]
  refine ⟨32183699057226485002989121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42911598742968646670652161 32183699057226485002989121)
  ·
    refine ⟨24137774292919863752241841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32183699057226485002989121 24137774292919863752241841)
    ·
      refine ⟨18103330719689897814181381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24137774292919863752241841 18103330719689897814181381)
      ·
        refine ⟨3394374509941855840159009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18103330719689897814181381 3394374509941855840159009)
        ·
          refine ⟨2545780882456391880119257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3394374509941855840159009 2545780882456391880119257)
          ·
            refine ⟨1909335661842293910089443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2545780882456391880119257 1909335661842293910089443)
            ·
              refine ⟨2864003492763440865134165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1909335661842293910089443 2864003492763440865134165)
              ·
                refine ⟨33562540930821572638291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2864003492763440865134165 33562540930821572638291)
                ·
                  rfl

theorem cell23_1764796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 8].length) (baseStart_1764796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764796 prefixEnd_1764796 := by exact prefixLift 1764796
  have htrace : WordTrace (prefixWord ++ tailWord_1764796) baseStart_1764796 baseEnd_1764796 := by
    simpa [prefixWord, tailWord_1764796, baseEnd_1764796] using wordTrace_append hprefix tailTrace_1764796
  have hstable : (prefixWord ++ tailWord_1764796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764796).length < 2 ^ (prefixWord ++ tailWord_1764796).sum := by decide
  have hdescent : baseEnd_1764796 < baseStart_1764796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764833 : List Nat := [1, 2, 3, 1, 2, 4, 1, 3, 1, 3, 2]
def baseStart_1764833 : Nat := 118140960795 + 1764833 * 2 ^ 59
def prefixEnd_1764833 : Nat := 4983230072969 + 3 ^ 40 * 1764833 * 2
def baseEnd_1764833 : Nat := 906207603916398816471187

theorem tailTrace_1764833 : CollatzResearch.WordTrace tailWord_1764833 prefixEnd_1764833 906207603916398816471187 := by
  unfold tailWord_1764833
  simp only [CollatzResearch.WordTrace]
  refine ⟨64368747615318925325075153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42912498410212616883383435 64368747615318925325075153)
  ·
    refine ⟨48276560711489193993806365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64368747615318925325075153 48276560711489193993806365)
    ·
      refine ⟨18103710266808447747677387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48276560711489193993806365 18103710266808447747677387)
      ·
        refine ⟨27155565400212671621516081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18103710266808447747677387 27155565400212671621516081)
        ·
          refine ⟨20366674050159503716137061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27155565400212671621516081 20366674050159503716137061)
          ·
            refine ⟨3818751384404906946775699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20366674050159503716137061 3818751384404906946775699)
            ·
              refine ⟨5728127076607360420163549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3818751384404906946775699 5728127076607360420163549)
              ·
                refine ⟨2148047653727760157561331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5728127076607360420163549 2148047653727760157561331)
                ·
                  refine ⟨3222071480591640236341997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2148047653727760157561331 3222071480591640236341997)
                  ·
                    refine ⟨1208276805221865088628249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3222071480591640236341997 1208276805221865088628249)
                    ·
                      refine ⟨906207603916398816471187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1208276805221865088628249 906207603916398816471187)
                      ·
                        rfl

theorem cell23_1764833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_1764833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764833 prefixEnd_1764833 := by exact prefixLift 1764833
  have htrace : WordTrace (prefixWord ++ tailWord_1764833) baseStart_1764833 baseEnd_1764833 := by
    simpa [prefixWord, tailWord_1764833, baseEnd_1764833] using wordTrace_append hprefix tailTrace_1764833
  have hstable : (prefixWord ++ tailWord_1764833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764833).length < 2 ^ (prefixWord ++ tailWord_1764833).sum := by decide
  have hdescent : baseEnd_1764833 < baseStart_1764833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764839 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 2, 6]
def baseStart_1764839 : Nat := 118140960795 + 1764839 * 2 ^ 59
def prefixEnd_1764839 : Nat := 4983230072969 + 3 ^ 40 * 1764839 * 2
def baseEnd_1764839 : Nat := 302070228266775264332053

theorem tailTrace_1764839 : CollatzResearch.WordTrace tailWord_1764839 prefixEnd_1764839 302070228266775264332053 := by
  unfold tailWord_1764839
  simp only [CollatzResearch.WordTrace]
  refine ⟨64368966453297188349793571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42912644302198125566529047 64368966453297188349793571)
  ·
    refine ⟨96553449679945782524690357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64368966453297188349793571 96553449679945782524690357)
    ·
      refine ⟨9051885907494917111689721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96553449679945782524690357 9051885907494917111689721)
      ·
        refine ⟨6788914430621187833767291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9051885907494917111689721 6788914430621187833767291)
        ·
          refine ⟨10183371645931781750650937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6788914430621187833767291 10183371645931781750650937)
          ·
            refine ⟨7637528734448836312988203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10183371645931781750650937 7637528734448836312988203)
            ·
              refine ⟨11456293101673254469482305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7637528734448836312988203 11456293101673254469482305)
              ·
                refine ⟨8592219826254940852111729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11456293101673254469482305 8592219826254940852111729)
                ·
                  refine ⟨6444164869691205639083797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8592219826254940852111729 6444164869691205639083797)
                  ·
                    refine ⟨302070228266775264332053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6444164869691205639083797 302070228266775264332053)
                    ·
                      rfl

theorem cell23_1764839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_1764839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764839 prefixEnd_1764839 := by exact prefixLift 1764839
  have htrace : WordTrace (prefixWord ++ tailWord_1764839) baseStart_1764839 baseEnd_1764839 := by
    simpa [prefixWord, tailWord_1764839, baseEnd_1764839] using wordTrace_append hprefix tailTrace_1764839
  have hstable : (prefixWord ++ tailWord_1764839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764839).length < 2 ^ (prefixWord ++ tailWord_1764839).sum := by decide
  have hdescent : baseEnd_1764839 < baseStart_1764839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764936 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 6, 4, 2]
def baseStart_1764936 : Nat := 118140960795 + 1764936 * 2 ^ 59
def prefixEnd_1764936 : Nat := 4983230072969 + 3 ^ 40 * 1764936 * 2
def baseEnd_1764936 : Nat := 906260492423811913483213

theorem tailTrace_1764936 : CollatzResearch.WordTrace tailWord_1764936 prefixEnd_1764936 906260492423811913483213 := by
  unfold tailWord_1764936
  simp only [CollatzResearch.WordTrace]
  refine ⟨32186252166972886958037331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42915002889297182610716441 32186252166972886958037331)
  ·
    refine ⟨48279378250459330437055997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32186252166972886958037331 48279378250459330437055997)
    ·
      refine ⟨18104766843922248913895999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48279378250459330437055997 18104766843922248913895999)
      ·
        refine ⟨27157150265883373370843999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18104766843922248913895999 27157150265883373370843999)
        ·
          refine ⟨40735725398825060056265999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27157150265883373370843999 40735725398825060056265999)
          ·
            refine ⟨61103588098237590084398999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40735725398825060056265999 61103588098237590084398999)
            ·
              refine ⟨91655382147356385126598499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61103588098237590084398999 91655382147356385126598499)
              ·
                refine ⟨137483073221034577689897749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91655382147356385126598499 137483073221034577689897749)
                ·
                  refine ⟨6444519057235995829213957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137483073221034577689897749 6444519057235995829213957)
                  ·
                    refine ⟨1208347323231749217977617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6444519057235995829213957 1208347323231749217977617)
                    ·
                      refine ⟨906260492423811913483213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1208347323231749217977617 906260492423811913483213)
                      ·
                        rfl

theorem cell23_1764936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_1764936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764936 prefixEnd_1764936 := by exact prefixLift 1764936
  have htrace : WordTrace (prefixWord ++ tailWord_1764936) baseStart_1764936 baseEnd_1764936 := by
    simpa [prefixWord, tailWord_1764936, baseEnd_1764936] using wordTrace_append hprefix tailTrace_1764936
  have hstable : (prefixWord ++ tailWord_1764936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764936).length < 2 ^ (prefixWord ++ tailWord_1764936).sum := by decide
  have hdescent : baseEnd_1764936 < baseStart_1764936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764949 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_1764949 : Nat := 118140960795 + 1764949 * 2 ^ 59
def prefixEnd_1764949 : Nat := 4983230072969 + 3 ^ 40 * 1764949 * 2
def baseEnd_1764949 : Nat := 906267167672320362620653

theorem tailTrace_1764949 : CollatzResearch.WordTrace tailWord_1764949 prefixEnd_1764949 906267167672320362620653 := by
  unfold tailWord_1764949
  simp only [CollatzResearch.WordTrace]
  refine ⟨64372978482898677136297901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42915318988599118090865267 64372978482898677136297901)
  ·
    refine ⟨24139866931087003926111713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64372978482898677136297901 24139866931087003926111713)
    ·
      refine ⟨18104900198315252944583785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24139866931087003926111713 18104900198315252944583785)
      ·
        refine ⟨13578675148736439708437839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18104900198315252944583785 13578675148736439708437839)
        ·
          refine ⟨20368012723104659562656759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13578675148736439708437839 20368012723104659562656759)
          ·
            refine ⟨30552019084656989343985139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20368012723104659562656759 30552019084656989343985139)
            ·
              refine ⟨45828028626985484015977709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30552019084656989343985139 45828028626985484015977709)
              ·
                refine ⟨17185510735119556505991641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45828028626985484015977709 17185510735119556505991641)
                ·
                  refine ⟨12889133051339667379493731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17185510735119556505991641 12889133051339667379493731)
                  ·
                    refine ⟨19333699577009501069240597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12889133051339667379493731 19333699577009501069240597)
                    ·
                      refine ⟨906267167672320362620653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19333699577009501069240597 906267167672320362620653)
                      ·
                        rfl

theorem cell23_1764949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_1764949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764949 prefixEnd_1764949 := by exact prefixLift 1764949
  have htrace : WordTrace (prefixWord ++ tailWord_1764949) baseStart_1764949 baseEnd_1764949 := by
    simpa [prefixWord, tailWord_1764949, baseEnd_1764949] using wordTrace_append hprefix tailTrace_1764949
  have hstable : (prefixWord ++ tailWord_1764949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764949).length < 2 ^ (prefixWord ++ tailWord_1764949).sum := by decide
  have hdescent : baseEnd_1764949 < baseStart_1764949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764976 : List Nat := [2, 1, 1, 1, 6, 1, 2, 3, 6]
def baseStart_1764976 : Nat := 118140960795 + 1764976 * 2 ^ 59
def prefixEnd_1764976 : Nat := 4983230072969 + 3 ^ 40 * 1764976 * 2
def baseEnd_1764976 : Nat := 100697892405554639664781

theorem tailTrace_1764976 : CollatzResearch.WordTrace tailWord_1764976 prefixEnd_1764976 100697892405554639664781 := by
  unfold tailWord_1764976
  simp only [CollatzResearch.WordTrace]
  refine ⟨32186981626900430373765391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42915975502533907165020521 32186981626900430373765391)
  ·
    refine ⟨48280472440350645560648087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32186981626900430373765391 48280472440350645560648087)
    ·
      refine ⟨72420708660525968340972131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48280472440350645560648087 72420708660525968340972131)
      ·
        refine ⟨108631062990788952511458197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72420708660525968340972131 108631062990788952511458197)
        ·
          refine ⟨5092081077693232148974603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 108631062990788952511458197 5092081077693232148974603)
          ·
            refine ⟨7638121616539848223461905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5092081077693232148974603 7638121616539848223461905)
            ·
              refine ⟨5728591212404886167596429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7638121616539848223461905 5728591212404886167596429)
              ·
                refine ⟨2148221704651832312848661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5728591212404886167596429 2148221704651832312848661)
                ·
                  refine ⟨100697892405554639664781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2148221704651832312848661 100697892405554639664781)
                  ·
                    rfl

theorem cell23_1764976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 6].length) (baseStart_1764976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1764976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1764976 prefixEnd_1764976 := by exact prefixLift 1764976
  have htrace : WordTrace (prefixWord ++ tailWord_1764976) baseStart_1764976 baseEnd_1764976 := by
    simpa [prefixWord, tailWord_1764976, baseEnd_1764976] using wordTrace_append hprefix tailTrace_1764976
  have hstable : (prefixWord ++ tailWord_1764976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764976).length < 2 ^ (prefixWord ++ tailWord_1764976).sum := by decide
  have hdescent : baseEnd_1764976 < baseStart_1764976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765010 : List Nat := [3, 2, 3, 1, 3, 2, 1, 2, 6]
def baseStart_1765010 : Nat := 118140960795 + 1765010 * 2 ^ 59
def prefixEnd_1765010 : Nat := 4983230072969 + 3 ^ 40 * 1765010 * 2
def baseEnd_1765010 : Nat := 100699832221360513773097

theorem tailTrace_1765010 : CollatzResearch.WordTrace tailWord_1765010 prefixEnd_1765010 100699832221360513773097 := by
  unfold tailWord_1765010
  simp only [CollatzResearch.WordTrace]
  refine ⟨16093800833919421138567121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42916802223785123036178989 16093800833919421138567121)
  ·
    refine ⟨12070350625439565853925341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16093800833919421138567121 12070350625439565853925341)
    ·
      refine ⟨4526381484539837195222003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12070350625439565853925341 4526381484539837195222003)
      ·
        refine ⟨6789572226809755792833005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4526381484539837195222003 6789572226809755792833005)
        ·
          refine ⟨2546089585053658422312377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6789572226809755792833005 2546089585053658422312377)
          ·
            refine ⟨1909567188790243816734283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2546089585053658422312377 1909567188790243816734283)
            ·
              refine ⟨2864350783185365725101425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1909567188790243816734283 2864350783185365725101425)
              ·
                refine ⟨2148263087389024293826069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2864350783185365725101425 2148263087389024293826069)
                ·
                  refine ⟨100699832221360513773097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2148263087389024293826069 100699832221360513773097)
                  ·
                    rfl

theorem cell23_1765010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_1765010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765010 prefixEnd_1765010 := by exact prefixLift 1765010
  have htrace : WordTrace (prefixWord ++ tailWord_1765010) baseStart_1765010 baseEnd_1765010 := by
    simpa [prefixWord, tailWord_1765010, baseEnd_1765010] using wordTrace_append hprefix tailTrace_1765010
  have hstable : (prefixWord ++ tailWord_1765010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765010).length < 2 ^ (prefixWord ++ tailWord_1765010).sum := by decide
  have hdescent : baseEnd_1765010 < baseStart_1765010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765013 : List Nat := [1, 3, 2, 1, 1, 1, 1, 6, 2, 3, 2]
def baseStart_1765013 : Nat := 118140960795 + 1765013 * 2 ^ 59
def prefixEnd_1765013 : Nat := 4983230072969 + 3 ^ 40 * 1765013 * 2
def baseEnd_1765013 : Nat := 906300030434208112220359

theorem tailTrace_1765013 : CollatzResearch.WordTrace tailWord_1765013 prefixEnd_1765013 906300030434208112220359 := by
  unfold tailWord_1765013
  simp only [CollatzResearch.WordTrace]
  refine ⟨64375312754666816066627693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42916875169777877377751795 64375312754666816066627693)
  ·
    refine ⟨24140742283000056024985385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64375312754666816066627693 24140742283000056024985385)
    ·
      refine ⟨18105556712250042018739039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24140742283000056024985385 18105556712250042018739039)
      ·
        refine ⟨27158335068375063028108559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18105556712250042018739039 27158335068375063028108559)
        ·
          refine ⟨40737502602562594542162839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27158335068375063028108559 40737502602562594542162839)
          ·
            refine ⟨61106253903843891813244259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40737502602562594542162839 61106253903843891813244259)
            ·
              refine ⟨91659380855765837719866389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61106253903843891813244259 91659380855765837719866389)
              ·
                refine ⟨4296533477614023643118737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91659380855765837719866389 4296533477614023643118737)
                ·
                  refine ⟨3222400108210517732339053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4296533477614023643118737 3222400108210517732339053)
                  ·
                    refine ⟨1208400040578944149627145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3222400108210517732339053 1208400040578944149627145)
                    ·
                      refine ⟨906300030434208112220359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1208400040578944149627145 906300030434208112220359)
                      ·
                        rfl

theorem cell23_1765013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_1765013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765013 prefixEnd_1765013 := by exact prefixLift 1765013
  have htrace : WordTrace (prefixWord ++ tailWord_1765013) baseStart_1765013 baseEnd_1765013 := by
    simpa [prefixWord, tailWord_1765013, baseEnd_1765013] using wordTrace_append hprefix tailTrace_1765013
  have hstable : (prefixWord ++ tailWord_1765013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765013).length < 2 ^ (prefixWord ++ tailWord_1765013).sum := by decide
  have hdescent : baseEnd_1765013 < baseStart_1765013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765043 : List Nat := [1, 1, 1, 2, 3, 3, 4, 2, 1, 1, 4]
def baseStart_1765043 : Nat := 118140960795 + 1765043 * 2 ^ 59
def prefixEnd_1765043 : Nat := 4983230072969 + 3 ^ 40 * 1765043 * 2
def baseEnd_1765043 : Nat := 906315434853842994845221

theorem tailTrace_1765043 : CollatzResearch.WordTrace tailWord_1765043 prefixEnd_1765043 906315434853842994845221 := by
  unfold tailWord_1765043
  simp only [CollatzResearch.WordTrace]
  refine ⟨64376406944558131190219783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42917604629705420793479855 64376406944558131190219783)
  ·
    refine ⟨96564610416837196785329675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64376406944558131190219783 96564610416837196785329675)
    ·
      refine ⟨144846915625255795177994513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96564610416837196785329675 144846915625255795177994513)
      ·
        refine ⟨108635186718941846383495885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144846915625255795177994513 108635186718941846383495885)
        ·
          refine ⟨40738195019603192393810957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108635186718941846383495885 40738195019603192393810957)
          ·
            refine ⟨15276823132351197147679109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40738195019603192393810957 15276823132351197147679109)
            ·
              refine ⟨2864404337315849465189833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15276823132351197147679109 2864404337315849465189833)
              ·
                refine ⟨2148303252986887098892375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2864404337315849465189833 2148303252986887098892375)
                ·
                  refine ⟨3222454879480330648338563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2148303252986887098892375 3222454879480330648338563)
                  ·
                    refine ⟨4833682319220495972507845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3222454879480330648338563 4833682319220495972507845)
                    ·
                      refine ⟨906315434853842994845221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4833682319220495972507845 906315434853842994845221)
                      ·
                        rfl

theorem cell23_1765043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 1, 4].length) (baseStart_1765043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765043 prefixEnd_1765043 := by exact prefixLift 1765043
  have htrace : WordTrace (prefixWord ++ tailWord_1765043) baseStart_1765043 baseEnd_1765043 := by
    simpa [prefixWord, tailWord_1765043, baseEnd_1765043] using wordTrace_append hprefix tailTrace_1765043
  have hstable : (prefixWord ++ tailWord_1765043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765043).length < 2 ^ (prefixWord ++ tailWord_1765043).sum := by decide
  have hdescent : baseEnd_1765043 < baseStart_1765043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765054 : List Nat := [4, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3]
def baseStart_1765054 : Nat := 118140960795 + 1765054 * 2 ^ 59
def prefixEnd_1765054 : Nat := 4983230072969 + 3 ^ 40 * 1765054 * 2
def baseEnd_1765054 : Nat := 906321083141042451807671

theorem tailTrace_1765054 : CollatzResearch.WordTrace tailWord_1765054 prefixEnd_1765054 906321083141042451807671 := by
  unfold tailWord_1765054
  simp only [CollatzResearch.WordTrace]
  refine ⟨8047101018439785008608777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42917872098345520045913477 8047101018439785008608777)
  ·
    refine ⟨6035325763829838756456583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8047101018439785008608777 6035325763829838756456583)
    ·
      refine ⟨9052988645744758134684875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6035325763829838756456583 9052988645744758134684875)
      ·
        refine ⟨13579482968617137202027313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9052988645744758134684875 13579482968617137202027313)
        ·
          refine ⟨10184612226462852901520485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13579482968617137202027313 10184612226462852901520485)
          ·
            refine ⟨1909614792461784919035091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10184612226462852901520485 1909614792461784919035091)
            ·
              refine ⟨2864422188692677378552637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1909614792461784919035091 2864422188692677378552637)
              ·
                refine ⟨1074158320759754016957239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2864422188692677378552637 1074158320759754016957239)
                ·
                  refine ⟨1611237481139631025435859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1074158320759754016957239 1611237481139631025435859)
                  ·
                    refine ⟨2416856221709446538153789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1611237481139631025435859 2416856221709446538153789)
                    ·
                      refine ⟨906321083141042451807671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2416856221709446538153789 906321083141042451807671)
                      ·
                        rfl

theorem cell23_1765054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_1765054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765054 prefixEnd_1765054 := by exact prefixLift 1765054
  have htrace : WordTrace (prefixWord ++ tailWord_1765054) baseStart_1765054 baseEnd_1765054 := by
    simpa [prefixWord, tailWord_1765054, baseEnd_1765054] using wordTrace_append hprefix tailTrace_1765054
  have hstable : (prefixWord ++ tailWord_1765054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765054).length < 2 ^ (prefixWord ++ tailWord_1765054).sum := by decide
  have hdescent : baseEnd_1765054 < baseStart_1765054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765056 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 4]
def baseStart_1765056 : Nat := 118140960795 + 1765056 * 2 ^ 59
def prefixEnd_1765056 : Nat := 4983230072969 + 3 ^ 40 * 1765056 * 2
def baseEnd_1765056 : Nat := 906322110102351443982661

theorem tailTrace_1765056 : CollatzResearch.WordTrace tailWord_1765056 prefixEnd_1765056 906322110102351443982661 := by
  unfold tailWord_1765056
  simp only [CollatzResearch.WordTrace]
  refine ⟨32188440546755517205221511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42917920729007356273628681 32188440546755517205221511)
  ·
    refine ⟨48282660820133275807832267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32188440546755517205221511 48282660820133275807832267)
    ·
      refine ⟨72423991230199913711748401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48282660820133275807832267 72423991230199913711748401)
      ·
        refine ⟨54317993422649935283811301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72423991230199913711748401 54317993422649935283811301)
        ·
          refine ⟨10184623766746862865714619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54317993422649935283811301 10184623766746862865714619)
          ·
            refine ⟨15276935650120294298571929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10184623766746862865714619 15276935650120294298571929)
            ·
              refine ⟨11457701737590220723928947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15276935650120294298571929 11457701737590220723928947)
              ·
                refine ⟨17186552606385331085893421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11457701737590220723928947 17186552606385331085893421)
                ·
                  refine ⟨6444957227394499157210033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17186552606385331085893421 6444957227394499157210033)
                  ·
                    refine ⟨4833717920545874367907525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6444957227394499157210033 4833717920545874367907525)
                    ·
                      refine ⟨906322110102351443982661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4833717920545874367907525 906322110102351443982661)
                      ·
                        rfl

theorem cell23_1765056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_1765056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765056 prefixEnd_1765056 := by exact prefixLift 1765056
  have htrace : WordTrace (prefixWord ++ tailWord_1765056) baseStart_1765056 baseEnd_1765056 := by
    simpa [prefixWord, tailWord_1765056, baseEnd_1765056] using wordTrace_append hprefix tailTrace_1765056
  have hstable : (prefixWord ++ tailWord_1765056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765056).length < 2 ^ (prefixWord ++ tailWord_1765056).sum := by decide
  have hdescent : baseEnd_1765056 < baseStart_1765056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765063 : List Nat := [1, 1, 4, 1, 1, 1, 3, 5, 1, 2, 3]
def baseStart_1765063 : Nat := 118140960795 + 1765063 * 2 ^ 59
def prefixEnd_1765063 : Nat := 4983230072969 + 3 ^ 40 * 1765063 * 2
def baseEnd_1765063 : Nat := 906325704466932916595129

theorem tailTrace_1765063 : CollatzResearch.WordTrace tailWord_1765063 prefixEnd_1765063 906325704466932916595129 := by
  unfold tailWord_1765063
  simp only [CollatzResearch.WordTrace]
  refine ⟨64377136404485674605947843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42918090936323783070631895 64377136404485674605947843)
  ·
    refine ⟨96565704606728511908921765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64377136404485674605947843 96565704606728511908921765)
    ·
      refine ⟨18106069613761595982922831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96565704606728511908921765 18106069613761595982922831)
      ·
        refine ⟨27159104420642393974384247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18106069613761595982922831 27159104420642393974384247)
        ·
          refine ⟨40738656630963590961576371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27159104420642393974384247 40738656630963590961576371)
          ·
            refine ⟨61107984946445386442364557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40738656630963590961576371 61107984946445386442364557)
            ·
              refine ⟨22915494354917019915886709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61107984946445386442364557 22915494354917019915886709)
              ·
                refine ⟨2148327595773470617114379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22915494354917019915886709 2148327595773470617114379)
                ·
                  refine ⟨3222491393660205925671569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2148327595773470617114379 3222491393660205925671569)
                  ·
                    refine ⟨2416868545245154444253677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3222491393660205925671569 2416868545245154444253677)
                    ·
                      refine ⟨906325704466932916595129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2416868545245154444253677 906325704466932916595129)
                      ·
                        rfl

theorem cell23_1765063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_1765063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765063 prefixEnd_1765063 := by exact prefixLift 1765063
  have htrace : WordTrace (prefixWord ++ tailWord_1765063) baseStart_1765063 baseEnd_1765063 := by
    simpa [prefixWord, tailWord_1765063, baseEnd_1765063] using wordTrace_append hprefix tailTrace_1765063
  have hstable : (prefixWord ++ tailWord_1765063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765063).length < 2 ^ (prefixWord ++ tailWord_1765063).sum := by decide
  have hdescent : baseEnd_1765063 < baseStart_1765063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765093 : List Nat := [1, 3, 1, 4, 1, 1, 2, 3, 1, 3, 3]
def baseStart_1765093 : Nat := 118140960795 + 1765093 * 2 ^ 59
def prefixEnd_1765093 : Nat := 4983230072969 + 3 ^ 40 * 1765093 * 2
def baseEnd_1765093 : Nat := 906341108886567799219991

theorem tailTrace_1765093 : CollatzResearch.WordTrace tailWord_1765093 prefixEnd_1765093 906341108886567799219991 := by
  unfold tailWord_1765093
  simp only [CollatzResearch.WordTrace]
  refine ⟨64378230594376989729539933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42918820396251326486359955 64378230594376989729539933)
  ·
    refine ⟨24141836472891371148577475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64378230594376989729539933 24141836472891371148577475)
    ·
      refine ⟨36212754709337056722866213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24141836472891371148577475 36212754709337056722866213)
      ·
        refine ⟨6789891508000698135537415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36212754709337056722866213 6789891508000698135537415)
        ·
          refine ⟨10184837262001047203306123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6789891508000698135537415 10184837262001047203306123)
          ·
            refine ⟨15277255893001570804959185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10184837262001047203306123 15277255893001570804959185)
            ·
              refine ⟨11457941919751178103719389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15277255893001570804959185 11457941919751178103719389)
              ·
                refine ⟨4296728219906691788894771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11457941919751178103719389 4296728219906691788894771)
                ·
                  refine ⟨6445092329860037683342157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4296728219906691788894771 6445092329860037683342157)
                  ·
                    refine ⟨2416909623697514131253309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6445092329860037683342157 2416909623697514131253309)
                    ·
                      refine ⟨906341108886567799219991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2416909623697514131253309 906341108886567799219991)
                      ·
                        rfl

theorem cell23_1765093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_1765093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765093 prefixEnd_1765093 := by exact prefixLift 1765093
  have htrace : WordTrace (prefixWord ++ tailWord_1765093) baseStart_1765093 baseEnd_1765093 := by
    simpa [prefixWord, tailWord_1765093, baseEnd_1765093] using wordTrace_append hprefix tailTrace_1765093
  have hstable : (prefixWord ++ tailWord_1765093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765093).length < 2 ^ (prefixWord ++ tailWord_1765093).sum := by decide
  have hdescent : baseEnd_1765093 < baseStart_1765093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765110 : List Nat := [5, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_1765110 : Nat := 118140960795 + 1765110 * 2 ^ 59
def prefixEnd_1765110 : Nat := 4983230072969 + 3 ^ 40 * 1765110 * 2
def baseEnd_1765110 : Nat := 906349838057694232707413

theorem tailTrace_1765110 : CollatzResearch.WordTrace tailWord_1765110 prefixEnd_1765110 906349838057694232707413 := by
  unfold tailWord_1765110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4023678164707212602056799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42919233756876934421939189 4023678164707212602056799)
  ·
    refine ⟨6035517247060818903085199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4023678164707212602056799 6035517247060818903085199)
    ·
      refine ⟨9053275870591228354627799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6035517247060818903085199 9053275870591228354627799)
      ·
        refine ⟨13579913805886842531941699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9053275870591228354627799 13579913805886842531941699)
        ·
          refine ⟨20369870708830263797912549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13579913805886842531941699 20369870708830263797912549)
          ·
            refine ⟨3819350757905674462108603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20369870708830263797912549 3819350757905674462108603)
            ·
              refine ⟨5729026136858511693162905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3819350757905674462108603 5729026136858511693162905)
              ·
                refine ⟨4296769602643883769872179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5729026136858511693162905 4296769602643883769872179)
                ·
                  refine ⟨6445154403965825654808269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4296769602643883769872179 6445154403965825654808269)
                  ·
                    refine ⟨2416932901487184620553101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6445154403965825654808269 2416932901487184620553101)
                    ·
                      refine ⟨906349838057694232707413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2416932901487184620553101 906349838057694232707413)
                      ·
                        rfl

theorem cell23_1765110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_1765110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765110 prefixEnd_1765110 := by exact prefixLift 1765110
  have htrace : WordTrace (prefixWord ++ tailWord_1765110) baseStart_1765110 baseEnd_1765110 := by
    simpa [prefixWord, tailWord_1765110, baseEnd_1765110] using wordTrace_append hprefix tailTrace_1765110
  have hstable : (prefixWord ++ tailWord_1765110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765110).length < 2 ^ (prefixWord ++ tailWord_1765110).sum := by decide
  have hdescent : baseEnd_1765110 < baseStart_1765110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765143 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 2, 6]
def baseStart_1765143 : Nat := 118140960795 + 1765143 * 2 ^ 59
def prefixEnd_1765143 : Nat := 4983230072969 + 3 ^ 40 * 1765143 * 2
def baseEnd_1765143 : Nat := 302122260973097534531587

theorem tailTrace_1765143 : CollatzResearch.WordTrace tailWord_1765143 prefixEnd_1765143 302122260973097534531587 := by
  unfold tailWord_1765143
  simp only [CollatzResearch.WordTrace]
  refine ⟨64380054244195848268860083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42920036162797232179240055 64380054244195848268860083)
  ·
    refine ⟨96570081366293772403290125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64380054244195848268860083 96570081366293772403290125)
    ·
      refine ⟨36213780512360164651233797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96570081366293772403290125 36213780512360164651233797)
      ·
        refine ⟨6790083846067530872106337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36213780512360164651233797 6790083846067530872106337)
        ·
          refine ⟨5092562884550648154079753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6790083846067530872106337 5092562884550648154079753)
          ·
            refine ⟨3819422163412986115559815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5092562884550648154079753 3819422163412986115559815)
            ·
              refine ⟨5729133245119479173339723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3819422163412986115559815 5729133245119479173339723)
              ·
                refine ⟨8593699867679218760009585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5729133245119479173339723 8593699867679218760009585)
                ·
                  refine ⟨6445274900759414070007189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8593699867679218760009585 6445274900759414070007189)
                  ·
                    refine ⟨302122260973097534531587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6445274900759414070007189 302122260973097534531587)
                    ·
                      rfl

theorem cell23_1765143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_1765143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765143 prefixEnd_1765143 := by exact prefixLift 1765143
  have htrace : WordTrace (prefixWord ++ tailWord_1765143) baseStart_1765143 baseEnd_1765143 := by
    simpa [prefixWord, tailWord_1765143, baseEnd_1765143] using wordTrace_append hprefix tailTrace_1765143
  have hstable : (prefixWord ++ tailWord_1765143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765143).length < 2 ^ (prefixWord ++ tailWord_1765143).sum := by decide
  have hdescent : baseEnd_1765143 < baseStart_1765143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765171 : List Nat := [1, 1, 1, 2, 8, 1, 2, 1, 1, 3, 2]
def baseStart_1765171 : Nat := 118140960795 + 1765171 * 2 ^ 59
def prefixEnd_1765171 : Nat := 4983230072969 + 3 ^ 40 * 1765171 * 2
def baseEnd_1765171 : Nat := 906381160377618494044633

theorem tailTrace_1765171 : CollatzResearch.WordTrace tailWord_1765171 prefixEnd_1765171 906381160377618494044633 := by
  unfold tailWord_1765171
  simp only [CollatzResearch.WordTrace]
  refine ⟨64381075488094409050879367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42920716992062939367252911 64381075488094409050879367)
  ·
    refine ⟨96571613232141613576319051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64381075488094409050879367 96571613232141613576319051)
    ·
      refine ⟨144857419848212420364478577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96571613232141613576319051 144857419848212420364478577)
      ·
        refine ⟨108643064886159315273358933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144857419848212420364478577 108643064886159315273358933)
        ·
          refine ⟨1273160916634679475859675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 108643064886159315273358933 1273160916634679475859675)
          ·
            refine ⟨1909741374952019213789513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273160916634679475859675 1909741374952019213789513)
            ·
              refine ⟨1432306031214014410342135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1909741374952019213789513 1432306031214014410342135)
              ·
                refine ⟨2148459046821021615513203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432306031214014410342135 2148459046821021615513203)
                ·
                  refine ⟨3222688570231532423269805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2148459046821021615513203 3222688570231532423269805)
                  ·
                    refine ⟨1208508213836824658726177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3222688570231532423269805 1208508213836824658726177)
                    ·
                      refine ⟨906381160377618494044633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1208508213836824658726177 906381160377618494044633)
                      ·
                        rfl

theorem cell23_1765171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 1, 3, 2].length) (baseStart_1765171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765171 prefixEnd_1765171 := by exact prefixLift 1765171
  have htrace : WordTrace (prefixWord ++ tailWord_1765171) baseStart_1765171 baseEnd_1765171 := by
    simpa [prefixWord, tailWord_1765171, baseEnd_1765171] using wordTrace_append hprefix tailTrace_1765171
  have hstable : (prefixWord ++ tailWord_1765171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765171).length < 2 ^ (prefixWord ++ tailWord_1765171).sum := by decide
  have hdescent : baseEnd_1765171 < baseStart_1765171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765223 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_1765223 : Nat := 118140960795 + 1765223 * 2 ^ 59
def prefixEnd_1765223 : Nat := 4983230072969 + 3 ^ 40 * 1765223 * 2
def baseEnd_1765223 : Nat := 906407861371652290594393

theorem tailTrace_1765223 : CollatzResearch.WordTrace tailWord_1765223 prefixEnd_1765223 906407861371652290594393 := by
  unfold tailWord_1765223
  simp only [CollatzResearch.WordTrace]
  refine ⟨64382972083906021931772323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42921981389270681287848215 64382972083906021931772323)
  ·
    refine ⟨96574458125859032897658485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64382972083906021931772323 96574458125859032897658485)
    ·
      refine ⟨9053855449299284334155483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96574458125859032897658485 9053855449299284334155483)
      ·
        refine ⟨13580783173948926501233225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9053855449299284334155483 13580783173948926501233225)
        ·
          refine ⟨10185587380461694875924919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13580783173948926501233225 10185587380461694875924919)
          ·
            refine ⟨15278381070692542313887379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10185587380461694875924919 15278381070692542313887379)
            ·
              refine ⟨22917571606038813470831069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15278381070692542313887379 22917571606038813470831069)
              ·
                refine ⟨8594089352264555051561651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22917571606038813470831069 8594089352264555051561651)
                ·
                  refine ⟨12891134028396832577342477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8594089352264555051561651 12891134028396832577342477)
                  ·
                    refine ⟨4834175260648812216503429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12891134028396832577342477 4834175260648812216503429)
                    ·
                      refine ⟨906407861371652290594393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4834175260648812216503429 906407861371652290594393)
                      ·
                        rfl

theorem cell23_1765223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_1765223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765223 prefixEnd_1765223 := by exact prefixLift 1765223
  have htrace : WordTrace (prefixWord ++ tailWord_1765223) baseStart_1765223 baseEnd_1765223 := by
    simpa [prefixWord, tailWord_1765223, baseEnd_1765223] using wordTrace_append hprefix tailTrace_1765223
  have hstable : (prefixWord ++ tailWord_1765223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765223).length < 2 ^ (prefixWord ++ tailWord_1765223).sum := by decide
  have hdescent : baseEnd_1765223 < baseStart_1765223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765273 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 2, 5, 3]
def baseStart_1765273 : Nat := 118140960795 + 1765273 * 2 ^ 59
def prefixEnd_1765273 : Nat := 4983230072969 + 3 ^ 40 * 1765273 * 2
def baseEnd_1765273 : Nat := 906433535404377094969163

theorem tailTrace_1765273 : CollatzResearch.WordTrace tailWord_1765273 prefixEnd_1765273 906433535404377094969163 := by
  unfold tailWord_1765273
  simp only [CollatzResearch.WordTrace]
  refine ⟨64384795733724880471092473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42923197155816586980728315 64384795733724880471092473)
  ·
    refine ⟨48288596800293660353319355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64384795733724880471092473 48288596800293660353319355)
    ·
      refine ⟨72432895200440490529979033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48288596800293660353319355 72432895200440490529979033)
      ·
        refine ⟨54324671400330367897484275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72432895200440490529979033 54324671400330367897484275)
        ·
          refine ⟨81487007100495551846226413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54324671400330367897484275 81487007100495551846226413)
          ·
            refine ⟨30557627662685831942334905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81487007100495551846226413 30557627662685831942334905)
            ·
              refine ⟨22918220747014373956751179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30557627662685831942334905 22918220747014373956751179)
              ·
                refine ⟨34377331120521560935126769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22918220747014373956751179 34377331120521560935126769)
                ·
                  refine ⟨25782998340391170701345077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34377331120521560935126769 25782998340391170701345077)
                  ·
                    refine ⟨2417156094411672253251101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25782998340391170701345077 2417156094411672253251101)
                    ·
                      refine ⟨906433535404377094969163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2417156094411672253251101 906433535404377094969163)
                      ·
                        rfl

theorem cell23_1765273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_1765273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765273 prefixEnd_1765273 := by exact prefixLift 1765273
  have htrace : WordTrace (prefixWord ++ tailWord_1765273) baseStart_1765273 baseEnd_1765273 := by
    simpa [prefixWord, tailWord_1765273, baseEnd_1765273] using wordTrace_append hprefix tailTrace_1765273
  have hstable : (prefixWord ++ tailWord_1765273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765273).length < 2 ^ (prefixWord ++ tailWord_1765273).sum := by decide
  have hdescent : baseEnd_1765273 < baseStart_1765273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765277 : List Nat := [1, 4, 2, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_1765277 : Nat := 118140960795 + 1765277 * 2 ^ 59
def prefixEnd_1765277 : Nat := 4983230072969 + 3 ^ 40 * 1765277 * 2
def baseEnd_1765277 : Nat := 906435589326995079319145

theorem tailTrace_1765277 : CollatzResearch.WordTrace tailWord_1765277 prefixEnd_1765277 906435589326995079319145 := by
  unfold tailWord_1765277
  simp only [CollatzResearch.WordTrace]
  refine ⟨64384941625710389154238085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42923294417140259436158723 64384941625710389154238085)
  ·
    refine ⟨12072176554820697966419641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64384941625710389154238085 12072176554820697966419641)
    ·
      refine ⟨9054132416115523474814731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12072176554820697966419641 9054132416115523474814731)
      ·
        refine ⟨13581198624173285212222097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9054132416115523474814731 13581198624173285212222097)
        ·
          refine ⟨10185898968129963909166573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13581198624173285212222097 10185898968129963909166573)
          ·
            refine ⟨3819712113048736465937465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10185898968129963909166573 3819712113048736465937465)
            ·
              refine ⟨2864784084786552349453099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3819712113048736465937465 2864784084786552349453099)
              ·
                refine ⟨4297176127179828524179649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2864784084786552349453099 4297176127179828524179649)
                ·
                  refine ⟨3222882095384871393134737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4297176127179828524179649 3222882095384871393134737)
                  ·
                    refine ⟨2417161571538653544851053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3222882095384871393134737 2417161571538653544851053)
                    ·
                      refine ⟨906435589326995079319145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2417161571538653544851053 906435589326995079319145)
                      ·
                        rfl

theorem cell23_1765277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_1765277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765277 prefixEnd_1765277 := by exact prefixLift 1765277
  have htrace : WordTrace (prefixWord ++ tailWord_1765277) baseStart_1765277 baseEnd_1765277 := by
    simpa [prefixWord, tailWord_1765277, baseEnd_1765277] using wordTrace_append hprefix tailTrace_1765277
  have hstable : (prefixWord ++ tailWord_1765277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765277).length < 2 ^ (prefixWord ++ tailWord_1765277).sum := by decide
  have hdescent : baseEnd_1765277 < baseStart_1765277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765301 : List Nat := [1, 3, 3, 2, 1, 4, 2, 2, 1, 4]
def baseStart_1765301 : Nat := 118140960795 + 1765301 * 2 ^ 59
def prefixEnd_1765301 : Nat := 4983230072969 + 3 ^ 40 * 1765301 * 2
def baseEnd_1765301 : Nat := 302149304287567661806345

theorem tailTrace_1765301 : CollatzResearch.WordTrace tailWord_1765301 prefixEnd_1765301 302149304287567661806345 := by
  unfold tailWord_1765301
  simp only [CollatzResearch.WordTrace]
  refine ⟨64385816977623441253111757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42923877985082294168741171 64385816977623441253111757)
  ·
    refine ⟨24144681366608790469916909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64385816977623441253111757 24144681366608790469916909)
    ·
      refine ⟨9054255512478296426218841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24144681366608790469916909 9054255512478296426218841)
      ·
        refine ⟨6790691634358722319664131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9054255512478296426218841 6790691634358722319664131)
        ·
          refine ⟨10186037451538083479496197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6790691634358722319664131 10186037451538083479496197)
          ·
            refine ⟨1909882022163390652405537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10186037451538083479496197 1909882022163390652405537)
            ·
              refine ⟨1432411516622542989304153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1909882022163390652405537 1432411516622542989304153)
              ·
                refine ⟨1074308637466907241978115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1432411516622542989304153 1074308637466907241978115)
                ·
                  refine ⟨1611462956200360862967173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1074308637466907241978115 1611462956200360862967173)
                  ·
                    refine ⟨302149304287567661806345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1611462956200360862967173 302149304287567661806345)
                    ·
                      rfl

theorem cell23_1765301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_1765301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765301 prefixEnd_1765301 := by exact prefixLift 1765301
  have htrace : WordTrace (prefixWord ++ tailWord_1765301) baseStart_1765301 baseEnd_1765301 := by
    simpa [prefixWord, tailWord_1765301, baseEnd_1765301] using wordTrace_append hprefix tailTrace_1765301
  have hstable : (prefixWord ++ tailWord_1765301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765301).length < 2 ^ (prefixWord ++ tailWord_1765301).sum := by decide
  have hdescent : baseEnd_1765301 < baseStart_1765301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765310 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_1765310 : Nat := 118140960795 + 1765310 * 2 ^ 59
def prefixEnd_1765310 : Nat := 4983230072969 + 3 ^ 40 * 1765310 * 2
def baseEnd_1765310 : Nat := 302150844729531150068831

theorem tailTrace_1765310 : CollatzResearch.WordTrace tailWord_1765310 prefixEnd_1765310 302150844729531150068831 := by
  unfold tailWord_1765310
  simp only [CollatzResearch.WordTrace]
  refine ⟨8048268154323854473773673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42924096823060557193459589 8048268154323854473773673)
  ·
    refine ⟨6036201115742890855330255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8048268154323854473773673 6036201115742890855330255)
    ·
      refine ⟨9054301673614336282995383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6036201115742890855330255 9054301673614336282995383)
      ·
        refine ⟨13581452510421504424493075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9054301673614336282995383 13581452510421504424493075)
        ·
          refine ⟨20372178765632256636739613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13581452510421504424493075 20372178765632256636739613)
          ·
            refine ⟨7639567037112096238777355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20372178765632256636739613 7639567037112096238777355)
            ·
              refine ⟨11459350555668144358166033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7639567037112096238777355 11459350555668144358166033)
              ·
                refine ⟨8594512916751108268624525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11459350555668144358166033 8594512916751108268624525)
                ·
                  refine ⟨3222942343781665600734197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8594512916751108268624525 3222942343781665600734197)
                  ·
                    refine ⟨302150844729531150068831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3222942343781665600734197 302150844729531150068831)
                    ·
                      rfl

theorem cell23_1765310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_1765310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765310 prefixEnd_1765310 := by exact prefixLift 1765310
  have htrace : WordTrace (prefixWord ++ tailWord_1765310) baseStart_1765310 baseEnd_1765310 := by
    simpa [prefixWord, tailWord_1765310, baseEnd_1765310] using wordTrace_append hprefix tailTrace_1765310
  have hstable : (prefixWord ++ tailWord_1765310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765310).length < 2 ^ (prefixWord ++ tailWord_1765310).sum := by decide
  have hdescent : baseEnd_1765310 < baseStart_1765310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765347 : List Nat := [1, 1, 1, 6, 1, 3, 1, 3, 1, 1, 4]
def baseStart_1765347 : Nat := 118140960795 + 1765347 * 2 ^ 59
def prefixEnd_1765347 : Nat := 4983230072969 + 3 ^ 40 * 1765347 * 2
def baseEnd_1765347 : Nat := 906471532972809805443823

theorem tailTrace_1765347 : CollatzResearch.WordTrace tailWord_1765347 prefixEnd_1765347 906471532972809805443823 := by
  unfold tailWord_1765347
  simp only [CollatzResearch.WordTrace]
  refine ⟨64387494735456791109286295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42924996490304527406190863 64387494735456791109286295)
  ·
    refine ⟨96581242103185186663929443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64387494735456791109286295 96581242103185186663929443)
    ·
      refine ⟨144871863154777779995894165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96581242103185186663929443 144871863154777779995894165)
      ·
        refine ⟨6790868585380208437307539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 144871863154777779995894165 6790868585380208437307539)
        ·
          refine ⟨10186302878070312655961309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6790868585380208437307539 10186302878070312655961309)
          ·
            refine ⟨3819863579276367245985491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10186302878070312655961309 3819863579276367245985491)
            ·
              refine ⟨5729795368914550868978237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3819863579276367245985491 5729795368914550868978237)
              ·
                refine ⟨2148673263342956575866839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5729795368914550868978237 2148673263342956575866839)
                ·
                  refine ⟨3223009895014434863800259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2148673263342956575866839 3223009895014434863800259)
                  ·
                    refine ⟨4834514842521652295700389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3223009895014434863800259 4834514842521652295700389)
                    ·
                      refine ⟨906471532972809805443823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4834514842521652295700389 906471532972809805443823)
                      ·
                        rfl

theorem cell23_1765347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_1765347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765347 prefixEnd_1765347 := by exact prefixLift 1765347
  have htrace : WordTrace (prefixWord ++ tailWord_1765347) baseStart_1765347 baseEnd_1765347 := by
    simpa [prefixWord, tailWord_1765347, baseEnd_1765347] using wordTrace_append hprefix tailTrace_1765347
  have hstable : (prefixWord ++ tailWord_1765347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765347).length < 2 ^ (prefixWord ++ tailWord_1765347).sum := by decide
  have hdescent : baseEnd_1765347 < baseStart_1765347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765374 : List Nat := [4, 2, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_1765374 : Nat := 118140960795 + 1765374 * 2 ^ 59
def prefixEnd_1765374 : Nat := 4983230072969 + 3 ^ 40 * 1765374 * 2
def baseEnd_1765374 : Nat := 302161798983493733268733

theorem tailTrace_1765374 : CollatzResearch.WordTrace tailWord_1765374 prefixEnd_1765374 302161798983493733268733 := by
  unfold tailWord_1765374
  simp only [CollatzResearch.WordTrace]
  refine ⟨8048559938294871840064897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42925653004239316480346117 8048559938294871840064897)
  ·
    refine ⟨6036419953721153880048673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8048559938294871840064897 6036419953721153880048673)
    ·
      refine ⟨4527314965290865410036505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6036419953721153880048673 4527314965290865410036505)
      ·
        refine ⟨3395486223968149057527379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4527314965290865410036505 3395486223968149057527379)
        ·
          refine ⟨5093229335952223586291069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3395486223968149057527379 5093229335952223586291069)
          ·
            refine ⟨1909961000982083844859151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5093229335952223586291069 1909961000982083844859151)
            ·
              refine ⟨2864941501473125767288727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1909961000982083844859151 2864941501473125767288727)
              ·
                refine ⟨4297412252209688650933091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2864941501473125767288727 4297412252209688650933091)
                ·
                  refine ⟨6446118378314532976399637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4297412252209688650933091 6446118378314532976399637)
                  ·
                    refine ⟨302161798983493733268733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6446118378314532976399637 302161798983493733268733)
                    ·
                      rfl

theorem cell23_1765374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_1765374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765374 prefixEnd_1765374 := by exact prefixLift 1765374
  have htrace : WordTrace (prefixWord ++ tailWord_1765374) baseStart_1765374 baseEnd_1765374 := by
    simpa [prefixWord, tailWord_1765374, baseEnd_1765374] using wordTrace_append hprefix tailTrace_1765374
  have hstable : (prefixWord ++ tailWord_1765374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765374).length < 2 ^ (prefixWord ++ tailWord_1765374).sum := by decide
  have hdescent : baseEnd_1765374 < baseStart_1765374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765410 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_1765410 : Nat := 118140960795 + 1765410 * 2 ^ 59
def prefixEnd_1765410 : Nat := 4983230072969 + 3 ^ 40 * 1765410 * 2
def baseEnd_1765410 : Nat := 906503882254043058956033

theorem tailTrace_1765410 : CollatzResearch.WordTrace tailWord_1765410 prefixEnd_1765410 906503882254043058956033 := by
  unfold tailWord_1765410
  simp only [CollatzResearch.WordTrace]
  refine ⟨16097448133557138217207421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42926528356152368579219789 16097448133557138217207421)
  ·
    refine ⟨6036543050083926831452783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16097448133557138217207421 6036543050083926831452783)
    ·
      refine ⟨9054814575125890247179175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6036543050083926831452783 9054814575125890247179175)
      ·
        refine ⟨13582221862688835370768763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9054814575125890247179175 13582221862688835370768763)
        ·
          refine ⟨20373332794033253056153145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13582221862688835370768763 20373332794033253056153145)
          ·
            refine ⟨15279999595524939792114859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20373332794033253056153145 15279999595524939792114859)
            ·
              refine ⟨22919999393287409688172289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15279999595524939792114859 22919999393287409688172289)
              ·
                refine ⟨17189999544965557266129217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22919999393287409688172289 17189999544965557266129217)
                ·
                  refine ⟨12892499658724167949596913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17189999544965557266129217 12892499658724167949596913)
                  ·
                    refine ⟨9669374744043125962197685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12892499658724167949596913 9669374744043125962197685)
                    ·
                      refine ⟨906503882254043058956033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9669374744043125962197685 906503882254043058956033)
                      ·
                        rfl

theorem cell23_1765410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_1765410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765410 prefixEnd_1765410 := by exact prefixLift 1765410
  have htrace : WordTrace (prefixWord ++ tailWord_1765410) baseStart_1765410 baseEnd_1765410 := by
    simpa [prefixWord, tailWord_1765410, baseEnd_1765410] using wordTrace_append hprefix tailTrace_1765410
  have hstable : (prefixWord ++ tailWord_1765410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765410).length < 2 ^ (prefixWord ++ tailWord_1765410).sum := by decide
  have hdescent : baseEnd_1765410 < baseStart_1765410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765415 : List Nat := [1, 1, 7, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_1765415 : Nat := 118140960795 + 1765415 * 2 ^ 59
def prefixEnd_1765415 : Nat := 4983230072969 + 3 ^ 40 * 1765415 * 2
def baseEnd_1765415 : Nat := 906506449657315539393511

theorem tailTrace_1765415 : CollatzResearch.WordTrace tailWord_1765415 prefixEnd_1765415 906506449657315539393511 := by
  unfold tailWord_1765415
  simp only [CollatzResearch.WordTrace]
  refine ⟨64389974899210438722761699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42926649932806959148507799 64389974899210438722761699)
  ·
    refine ⟨96584962348815658084142549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64389974899210438722761699 96584962348815658084142549)
    ·
      refine ⟨2263710055050366986347091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 96584962348815658084142549 2263710055050366986347091)
      ·
        refine ⟨3395565082575550479520637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2263710055050366986347091 3395565082575550479520637)
        ·
          refine ⟨1273336905965831429820239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3395565082575550479520637 1273336905965831429820239)
          ·
            refine ⟨1910005358948747144730359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273336905965831429820239 1910005358948747144730359)
            ·
              refine ⟨2865008038423120717095539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1910005358948747144730359 2865008038423120717095539)
              ·
                refine ⟨4297512057634681075643309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2865008038423120717095539 4297512057634681075643309)
                ·
                  refine ⟨1611567021613005403366241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4297512057634681075643309 1611567021613005403366241)
                  ·
                    refine ⟨1208675266209754052524681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1611567021613005403366241 1208675266209754052524681)
                    ·
                      refine ⟨906506449657315539393511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1208675266209754052524681 906506449657315539393511)
                      ·
                        rfl

theorem cell23_1765415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_1765415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765415 prefixEnd_1765415 := by exact prefixLift 1765415
  have htrace : WordTrace (prefixWord ++ tailWord_1765415) baseStart_1765415 baseEnd_1765415 := by
    simpa [prefixWord, tailWord_1765415, baseEnd_1765415] using wordTrace_append hprefix tailTrace_1765415
  have hstable : (prefixWord ++ tailWord_1765415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765415).length < 2 ^ (prefixWord ++ tailWord_1765415).sum := by decide
  have hdescent : baseEnd_1765415 < baseStart_1765415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765440 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 5]
def baseStart_1765440 : Nat := 118140960795 + 1765440 * 2 ^ 59
def prefixEnd_1765440 : Nat := 4983230072969 + 3 ^ 40 * 1765440 * 2
def baseEnd_1765440 : Nat := 906519286673677941580895

theorem tailTrace_1765440 : CollatzResearch.WordTrace tailWord_1765440 prefixEnd_1765440 906519286673677941580895 := by
  unfold tailWord_1765440
  simp only [CollatzResearch.WordTrace]
  refine ⟨32195443362059933996210887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42927257816079911994947849 32195443362059933996210887)
  ·
    refine ⟨48293165043089900994316331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32195443362059933996210887 48293165043089900994316331)
    ·
      refine ⟨72439747564634851491474497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48293165043089900994316331 72439747564634851491474497)
      ·
        refine ⟨54329810673476138618605873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72439747564634851491474497 54329810673476138618605873)
        ·
          refine ⟨40747358005107103963954405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54329810673476138618605873 40747358005107103963954405)
          ·
            refine ⟨7640129625957581993241451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40747358005107103963954405 7640129625957581993241451)
            ·
              refine ⟨11460194438936372989862177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7640129625957581993241451 11460194438936372989862177)
              ·
                refine ⟨8595145829202279742396633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11460194438936372989862177 8595145829202279742396633)
                ·
                  refine ⟨6446359371901709806797475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8595145829202279742396633 6446359371901709806797475)
                  ·
                    refine ⟨9669539057852564710196213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6446359371901709806797475 9669539057852564710196213)
                    ·
                      refine ⟨906519286673677941580895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9669539057852564710196213 906519286673677941580895)
                      ·
                        rfl

theorem cell23_1765440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_1765440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765440 prefixEnd_1765440 := by exact prefixLift 1765440
  have htrace : WordTrace (prefixWord ++ tailWord_1765440) baseStart_1765440 baseEnd_1765440 := by
    simpa [prefixWord, tailWord_1765440, baseEnd_1765440] using wordTrace_append hprefix tailTrace_1765440
  have hstable : (prefixWord ++ tailWord_1765440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765440).length < 2 ^ (prefixWord ++ tailWord_1765440).sum := by decide
  have hdescent : baseEnd_1765440 < baseStart_1765440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765441 : List Nat := [1, 2, 5, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_1765441 : Nat := 118140960795 + 1765441 * 2 ^ 59
def prefixEnd_1765441 : Nat := 4983230072969 + 3 ^ 40 * 1765441 * 2
def baseEnd_1765441 : Nat := 906519800154332437668391

theorem tailTrace_1765441 : CollatzResearch.WordTrace tailWord_1765441 prefixEnd_1765441 906519800154332437668391 := by
  unfold tailWord_1765441
  simp only [CollatzResearch.WordTrace]
  refine ⟨64390923197116245163208177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42927282131410830108805451 64390923197116245163208177)
  ·
    refine ⟨48293192397837183872406133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64390923197116245163208177 48293192397837183872406133)
    ·
      refine ⟨4527486787297235988038075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48293192397837183872406133 4527486787297235988038075)
      ·
        refine ⟨6791230180945853982057113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4527486787297235988038075 6791230180945853982057113)
        ·
          refine ⟨5093422635709390486542835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6791230180945853982057113 5093422635709390486542835)
          ·
            refine ⟨7640133953564085729814253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5093422635709390486542835 7640133953564085729814253)
            ·
              refine ⟨2865050232586532148680345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7640133953564085729814253 2865050232586532148680345)
              ·
                refine ⟨2148787674439899111510259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2865050232586532148680345 2148787674439899111510259)
                ·
                  refine ⟨3223181511659848667265389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2148787674439899111510259 3223181511659848667265389)
                  ·
                    refine ⟨1208693066872443250224521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3223181511659848667265389 1208693066872443250224521)
                    ·
                      refine ⟨906519800154332437668391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1208693066872443250224521 906519800154332437668391)
                      ·
                        rfl

theorem cell23_1765441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_1765441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765441 prefixEnd_1765441 := by exact prefixLift 1765441
  have htrace : WordTrace (prefixWord ++ tailWord_1765441) baseStart_1765441 baseEnd_1765441 := by
    simpa [prefixWord, tailWord_1765441, baseEnd_1765441] using wordTrace_append hprefix tailTrace_1765441
  have hstable : (prefixWord ++ tailWord_1765441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765441).length < 2 ^ (prefixWord ++ tailWord_1765441).sum := by decide
  have hdescent : baseEnd_1765441 < baseStart_1765441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765450 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_1765450 : Nat := 118140960795 + 1765450 * 2 ^ 59
def prefixEnd_1765450 : Nat := 4983230072969 + 3 ^ 40 * 1765450 * 2
def baseEnd_1765450 : Nat := 906524421480222902455849

theorem tailTrace_1765450 : CollatzResearch.WordTrace tailWord_1765450 prefixEnd_1765450 906524421480222902455849 := by
  unfold tailWord_1765450
  simp only [CollatzResearch.WordTrace]
  refine ⟨16097812863520909925071451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42927500969389093133523869 16097812863520909925071451)
  ·
    refine ⟨24146719295281364887607177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16097812863520909925071451 24146719295281364887607177)
    ·
      refine ⟨18110039471461023665705383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24146719295281364887607177 18110039471461023665705383)
      ·
        refine ⟨27165059207191535498558075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18110039471461023665705383 27165059207191535498558075)
        ·
          refine ⟨40747588810787303247837113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27165059207191535498558075 40747588810787303247837113)
          ·
            refine ⟨30560691608090477435877835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40747588810787303247837113 30560691608090477435877835)
            ·
              refine ⟨45841037412135716153816753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30560691608090477435877835 45841037412135716153816753)
              ·
                refine ⟨34380778059101787115362565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45841037412135716153816753 34380778059101787115362565)
                ·
                  refine ⟨6446395886081585084130481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34380778059101787115362565 6446395886081585084130481)
                  ·
                    refine ⟨4834796914561188813097861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6446395886081585084130481 4834796914561188813097861)
                    ·
                      refine ⟨906524421480222902455849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4834796914561188813097861 906524421480222902455849)
                      ·
                        rfl

theorem cell23_1765450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_1765450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765450 prefixEnd_1765450 := by exact prefixLift 1765450
  have htrace : WordTrace (prefixWord ++ tailWord_1765450) baseStart_1765450 baseEnd_1765450 := by
    simpa [prefixWord, tailWord_1765450, baseEnd_1765450] using wordTrace_append hprefix tailTrace_1765450
  have hstable : (prefixWord ++ tailWord_1765450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765450).length < 2 ^ (prefixWord ++ tailWord_1765450).sum := by decide
  have hdescent : baseEnd_1765450 < baseStart_1765450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765454 : List Nat := [4, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2]
def baseStart_1765454 : Nat := 118140960795 + 1765454 * 2 ^ 59
def prefixEnd_1765454 : Nat := 4983230072969 + 3 ^ 40 * 1765454 * 2
def baseEnd_1765454 : Nat := 906526475402840886805831

theorem tailTrace_1765454 : CollatzResearch.WordTrace tailWord_1765454 prefixEnd_1765454 906526475402840886805831 := by
  unfold tailWord_1765454
  simp only [CollatzResearch.WordTrace]
  refine ⟨8048924668258643547928927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42927598230712765588954277 8048924668258643547928927)
  ·
    refine ⟨12073387002387965321893391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8048924668258643547928927 12073387002387965321893391)
    ·
      refine ⟨18110080503581947982840087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12073387002387965321893391 18110080503581947982840087)
      ·
        refine ⟨27165120755372921974260131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18110080503581947982840087 27165120755372921974260131)
        ·
          refine ⟨40747681133059382961390197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27165120755372921974260131 40747681133059382961390197)
          ·
            refine ⟨3820095106224317152630331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40747681133059382961390197 3820095106224317152630331)
            ·
              refine ⟨5730142659336475728945497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3820095106224317152630331 5730142659336475728945497)
              ·
                refine ⟨4297606994502356796709123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5730142659336475728945497 4297606994502356796709123)
                ·
                  refine ⟨6446410491753535195063685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4297606994502356796709123 6446410491753535195063685)
                  ·
                    refine ⟨1208701967203787849074441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6446410491753535195063685 1208701967203787849074441)
                    ·
                      refine ⟨906526475402840886805831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1208701967203787849074441 906526475402840886805831)
                      ·
                        rfl

theorem cell23_1765454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_1765454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765454 prefixEnd_1765454 := by exact prefixLift 1765454
  have htrace : WordTrace (prefixWord ++ tailWord_1765454) baseStart_1765454 baseEnd_1765454 := by
    simpa [prefixWord, tailWord_1765454, baseEnd_1765454] using wordTrace_append hprefix tailTrace_1765454
  have hstable : (prefixWord ++ tailWord_1765454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765454).length < 2 ^ (prefixWord ++ tailWord_1765454).sum := by decide
  have hdescent : baseEnd_1765454 < baseStart_1765454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765458 : List Nat := [3, 2, 2, 1, 4, 1, 3, 1, 1, 3, 2]
def baseStart_1765458 : Nat := 118140960795 + 1765458 * 2 ^ 59
def prefixEnd_1765458 : Nat := 4983230072969 + 3 ^ 40 * 1765458 * 2
def baseEnd_1765458 : Nat := 906528529325458871155813

theorem tailTrace_1765458 : CollatzResearch.WordTrace tailWord_1765458 prefixEnd_1765458 906528529325458871155813 := by
  unfold tailWord_1765458
  simp only [CollatzResearch.WordTrace]
  refine ⟨16097885809513664266644257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42927695492036438044384685 16097885809513664266644257)
  ·
    refine ⟨12073414357135248199983193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16097885809513664266644257 12073414357135248199983193)
    ·
      refine ⟨9055060767851436149987395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12073414357135248199983193 9055060767851436149987395)
      ·
        refine ⟨13582591151777154224981093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9055060767851436149987395 13582591151777154224981093)
        ·
          refine ⟨2546735840958216417183955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13582591151777154224981093 2546735840958216417183955)
          ·
            refine ⟨3820103761437324625775933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2546735840958216417183955 3820103761437324625775933)
            ·
              refine ⟨1432538910538996734665975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3820103761437324625775933 1432538910538996734665975)
              ·
                refine ⟨2148808365808495101998963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432538910538996734665975 2148808365808495101998963)
                ·
                  refine ⟨3223212548712742652998445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2148808365808495101998963 3223212548712742652998445)
                  ·
                    refine ⟨1208704705767278494874417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3223212548712742652998445 1208704705767278494874417)
                    ·
                      refine ⟨906528529325458871155813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1208704705767278494874417 906528529325458871155813)
                      ·
                        rfl

theorem cell23_1765458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_1765458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765458 prefixEnd_1765458 := by exact prefixLift 1765458
  have htrace : WordTrace (prefixWord ++ tailWord_1765458) baseStart_1765458 baseEnd_1765458 := by
    simpa [prefixWord, tailWord_1765458, baseEnd_1765458] using wordTrace_append hprefix tailTrace_1765458
  have hstable : (prefixWord ++ tailWord_1765458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765458).length < 2 ^ (prefixWord ++ tailWord_1765458).sum := by decide
  have hdescent : baseEnd_1765458 < baseStart_1765458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765487 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 3]
def baseStart_1765487 : Nat := 118140960795 + 1765487 * 2 ^ 59
def prefixEnd_1765487 : Nat := 4983230072969 + 3 ^ 40 * 1765487 * 2
def baseEnd_1765487 : Nat := 906543420264439257693179

theorem tailTrace_1765487 : CollatzResearch.WordTrace tailWord_1765487 prefixEnd_1765487 906543420264439257693179 := by
  unfold tailWord_1765487
  simp only [CollatzResearch.WordTrace]
  refine ⟨64392600954949595019382715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42928400636633063346255143 64392600954949595019382715)
  ·
    refine ⟨96588901432424392529074073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64392600954949595019382715 96588901432424392529074073)
    ·
      refine ⟨72441676074318294396805555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96588901432424392529074073 72441676074318294396805555)
      ·
        refine ⟨108662514111477441595208333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72441676074318294396805555 108662514111477441595208333)
        ·
          refine ⟨40748442791804040598203125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108662514111477441595208333 40748442791804040598203125)
          ·
            refine ⟨3820166511731628806081543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40748442791804040598203125 3820166511731628806081543)
            ·
              refine ⟨5730249767597443209122315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3820166511731628806081543 5730249767597443209122315)
              ·
                refine ⟨8595374651396164813683473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5730249767597443209122315 8595374651396164813683473)
                ·
                  refine ⟨6446530988547123610262605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8595374651396164813683473 6446530988547123610262605)
                  ·
                    refine ⟨2417449120705171353848477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6446530988547123610262605 2417449120705171353848477)
                    ·
                      refine ⟨906543420264439257693179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2417449120705171353848477 906543420264439257693179)
                      ·
                        rfl

theorem cell23_1765487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 3].length) (baseStart_1765487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765487 prefixEnd_1765487 := by exact prefixLift 1765487
  have htrace : WordTrace (prefixWord ++ tailWord_1765487) baseStart_1765487 baseEnd_1765487 := by
    simpa [prefixWord, tailWord_1765487, baseEnd_1765487] using wordTrace_append hprefix tailTrace_1765487
  have hstable : (prefixWord ++ tailWord_1765487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765487).length < 2 ^ (prefixWord ++ tailWord_1765487).sum := by decide
  have hdescent : baseEnd_1765487 < baseStart_1765487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765507 : List Nat := [1, 1, 1, 3, 3, 3, 3, 1, 2, 5]
def baseStart_1765507 : Nat := 118140960795 + 1765507 * 2 ^ 59
def prefixEnd_1765507 : Nat := 4983230072969 + 3 ^ 40 * 1765507 * 2
def baseEnd_1765507 : Nat := 302184563292509726481029

theorem tailTrace_1765507 : CollatzResearch.WordTrace tailWord_1765507 prefixEnd_1765507 302184563292509726481029 := by
  unfold tailWord_1765507
  simp only [CollatzResearch.WordTrace]
  refine ⟨64393330414877138435110775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42928886943251425623407183 64393330414877138435110775)
  ·
    refine ⟨96589995622315707652666163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64393330414877138435110775 96589995622315707652666163)
    ·
      refine ⟨144884993433473561478999245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96589995622315707652666163 144884993433473561478999245)
      ·
        refine ⟨54331872537552585554624717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144884993433473561478999245 54331872537552585554624717)
        ·
          refine ⟨20374452201582219582984269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54331872537552585554624717 20374452201582219582984269)
          ·
            refine ⟨7640419575593332343619101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20374452201582219582984269 7640419575593332343619101)
            ·
              refine ⟨2865157340847499628857163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7640419575593332343619101 2865157340847499628857163)
              ·
                refine ⟨4297736011271249443285745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2865157340847499628857163 4297736011271249443285745)
                ·
                  refine ⟨3223302008453437082464309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4297736011271249443285745 3223302008453437082464309)
                  ·
                    refine ⟨302184563292509726481029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3223302008453437082464309 302184563292509726481029)
                    ·
                      rfl

theorem cell23_1765507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 5].length) (baseStart_1765507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765507 prefixEnd_1765507 := by exact prefixLift 1765507
  have htrace : WordTrace (prefixWord ++ tailWord_1765507) baseStart_1765507 baseEnd_1765507 := by
    simpa [prefixWord, tailWord_1765507, baseEnd_1765507] using wordTrace_append hprefix tailTrace_1765507
  have hstable : (prefixWord ++ tailWord_1765507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765507).length < 2 ^ (prefixWord ++ tailWord_1765507).sum := by decide
  have hdescent : baseEnd_1765507 < baseStart_1765507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765604 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 6, 3, 2]
def baseStart_1765604 : Nat := 118140960795 + 1765604 * 2 ^ 59
def prefixEnd_1765604 : Nat := 4983230072969 + 3 ^ 40 * 1765604 * 2
def baseEnd_1765604 : Nat := 906603497501015299930141

theorem tailTrace_1765604 : CollatzResearch.WordTrace tailWord_1765604 prefixEnd_1765604 906603497501015299930141 := by
  unfold tailWord_1765604
  simp only [CollatzResearch.WordTrace]
  refine ⟨32198434147762862000695933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42931245530350482667594577 32198434147762862000695933)
  ·
    refine ⟨12074412805411073250260975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32198434147762862000695933 12074412805411073250260975)
    ·
      refine ⟨18111619208116609875391463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12074412805411073250260975 18111619208116609875391463)
      ·
        refine ⟨27167428812174914813087195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18111619208116609875391463 27167428812174914813087195)
        ·
          refine ⟨40751143218262372219630793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27167428812174914813087195 40751143218262372219630793)
          ·
            refine ⟨30563357413696779164723095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40751143218262372219630793 30563357413696779164723095)
            ·
              refine ⟨45845036120545168747084643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30563357413696779164723095 45845036120545168747084643)
              ·
                refine ⟨68767554180817753120626965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45845036120545168747084643 68767554180817753120626965)
                ·
                  refine ⟨3223479102225832177529389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68767554180817753120626965 3223479102225832177529389)
                  ·
                    refine ⟨1208804663334687066573521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3223479102225832177529389 1208804663334687066573521)
                    ·
                      refine ⟨906603497501015299930141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1208804663334687066573521 906603497501015299930141)
                      ·
                        rfl

theorem cell23_1765604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_1765604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765604 prefixEnd_1765604 := by exact prefixLift 1765604
  have htrace : WordTrace (prefixWord ++ tailWord_1765604) baseStart_1765604 baseEnd_1765604 := by
    simpa [prefixWord, tailWord_1765604, baseEnd_1765604] using wordTrace_append hprefix tailTrace_1765604
  have hstable : (prefixWord ++ tailWord_1765604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765604).length < 2 ^ (prefixWord ++ tailWord_1765604).sum := by decide
  have hdescent : baseEnd_1765604 < baseStart_1765604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765637 : List Nat := [1, 3, 1, 1, 2, 1, 2, 5, 1, 1, 5]
def baseStart_1765637 : Nat := 118140960795 + 1765637 * 2 ^ 59
def prefixEnd_1765637 : Nat := 4983230072969 + 3 ^ 40 * 1765637 * 2
def baseEnd_1765637 : Nat := 906620442362613670817489

theorem tailTrace_1765637 : CollatzResearch.WordTrace tailWord_1765637 prefixEnd_1765637 906620442362613670817489 := by
  unfold tailWord_1765637
  simp only [CollatzResearch.WordTrace]
  refine ⟨64398071904406170637343165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42932047936270780424895443 64398071904406170637343165)
  ·
    refine ⟨24149276964152313989003687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64398071904406170637343165 24149276964152313989003687)
    ·
      refine ⟨36223915446228470983505531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24149276964152313989003687 36223915446228470983505531)
      ·
        refine ⟨54335873169342706475258297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36223915446228470983505531 54335873169342706475258297)
        ·
          refine ⟨40751904877007029856443723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54335873169342706475258297 40751904877007029856443723)
          ·
            refine ⟨61127857315510544784665585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40751904877007029856443723 61127857315510544784665585)
            ·
              refine ⟨45845892986632908588499189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61127857315510544784665585 45845892986632908588499189)
              ·
                refine ⟨4298052467496835180171799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45845892986632908588499189 4298052467496835180171799)
                ·
                  refine ⟨6447078701245252770257699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4298052467496835180171799 6447078701245252770257699)
                  ·
                    refine ⟨9670618051867879155386549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6447078701245252770257699 9670618051867879155386549)
                    ·
                      refine ⟨906620442362613670817489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9670618051867879155386549 906620442362613670817489)
                      ·
                        rfl

theorem cell23_1765637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_1765637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765637 prefixEnd_1765637 := by exact prefixLift 1765637
  have htrace : WordTrace (prefixWord ++ tailWord_1765637) baseStart_1765637 baseEnd_1765637 := by
    simpa [prefixWord, tailWord_1765637, baseEnd_1765637] using wordTrace_append hprefix tailTrace_1765637
  have hstable : (prefixWord ++ tailWord_1765637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765637).length < 2 ^ (prefixWord ++ tailWord_1765637).sum := by decide
  have hdescent : baseEnd_1765637 < baseStart_1765637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765661 : List Nat := [1, 4, 2, 3, 2, 1, 2, 1, 1, 6]
def baseStart_1765661 : Nat := 118140960795 + 1765661 * 2 ^ 59
def prefixEnd_1765661 : Nat := 4983230072969 + 3 ^ 40 * 1765661 * 2
def baseEnd_1765661 : Nat := 302210921966107192305793

theorem tailTrace_1765661 : CollatzResearch.WordTrace tailWord_1765661 prefixEnd_1765661 302210921966107192305793 := by
  unfold tailWord_1765661
  simp only [CollatzResearch.WordTrace]
  refine ⟨64398947256319222736216837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42932631504212815157477891 64398947256319222736216837)
  ·
    refine ⟨12074802610559854263040657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64398947256319222736216837 12074802610559854263040657)
    ·
      refine ⟨9056101957919890697280493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12074802610559854263040657 9056101957919890697280493)
      ·
        refine ⟨3396038234219959011480185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9056101957919890697280493 3396038234219959011480185)
        ·
          refine ⟨2547028675664969258610139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3396038234219959011480185 2547028675664969258610139)
          ·
            refine ⟨3820543013497453887915209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2547028675664969258610139 3820543013497453887915209)
            ·
              refine ⟨2865407260123090415936407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3820543013497453887915209 2865407260123090415936407)
              ·
                refine ⟨4298110890184635623904611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2865407260123090415936407 4298110890184635623904611)
                ·
                  refine ⟨6447166335276953435856917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4298110890184635623904611 6447166335276953435856917)
                  ·
                    refine ⟨302210921966107192305793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6447166335276953435856917 302210921966107192305793)
                    ·
                      rfl

theorem cell23_1765661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_1765661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765661 prefixEnd_1765661 := by exact prefixLift 1765661
  have htrace : WordTrace (prefixWord ++ tailWord_1765661) baseStart_1765661 baseEnd_1765661 := by
    simpa [prefixWord, tailWord_1765661, baseEnd_1765661] using wordTrace_append hprefix tailTrace_1765661
  have hstable : (prefixWord ++ tailWord_1765661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765661).length < 2 ^ (prefixWord ++ tailWord_1765661).sum := by decide
  have hdescent : baseEnd_1765661 < baseStart_1765661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765664 : List Nat := [2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 4]
def baseStart_1765664 : Nat := 118140960795 + 1765664 * 2 ^ 59
def prefixEnd_1765664 : Nat := 4983230072969 + 3 ^ 40 * 1765664 * 2
def baseEnd_1765664 : Nat := 906634306340285065179865

theorem tailTrace_1765664 : CollatzResearch.WordTrace tailWord_1765664 prefixEnd_1765664 906634306340285065179865 := by
  unfold tailWord_1765664
  simp only [CollatzResearch.WordTrace]
  refine ⟨32199528337654177124288023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42932704450205569499050697 32199528337654177124288023)
  ·
    refine ⟨48299292506481265686432035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32199528337654177124288023 48299292506481265686432035)
    ·
      refine ⟨72448938759721898529648053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48299292506481265686432035 72448938759721898529648053)
      ·
        refine ⟨6792088008723927987154505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72448938759721898529648053 6792088008723927987154505)
        ·
          refine ⟨5094066006542945990365879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6792088008723927987154505 5094066006542945990365879)
          ·
            refine ⟨7641099009814418985548819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5094066006542945990365879 7641099009814418985548819)
            ·
              refine ⟨11461648514721628478323229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7641099009814418985548819 11461648514721628478323229)
              ·
                refine ⟨4298118193020610679371211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11461648514721628478323229 4298118193020610679371211)
                ·
                  refine ⟨6447177289530916019056817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4298118193020610679371211 6447177289530916019056817)
                  ·
                    refine ⟨4835382967148187014292613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6447177289530916019056817 4835382967148187014292613)
                    ·
                      refine ⟨906634306340285065179865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4835382967148187014292613 906634306340285065179865)
                      ·
                        rfl

theorem cell23_1765664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_1765664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765664 prefixEnd_1765664 := by exact prefixLift 1765664
  have htrace : WordTrace (prefixWord ++ tailWord_1765664) baseStart_1765664 baseEnd_1765664 := by
    simpa [prefixWord, tailWord_1765664, baseEnd_1765664] using wordTrace_append hprefix tailTrace_1765664
  have hstable : (prefixWord ++ tailWord_1765664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765664).length < 2 ^ (prefixWord ++ tailWord_1765664).sum := by decide
  have hdescent : baseEnd_1765664 < baseStart_1765664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765668 : List Nat := [2, 3, 1, 3, 1, 3, 1, 2, 3, 2, 2]
def baseStart_1765668 : Nat := 118140960795 + 1765668 * 2 ^ 59
def prefixEnd_1765668 : Nat := 4983230072969 + 3 ^ 40 * 1765668 * 2
def baseEnd_1765668 : Nat := 906636360262903049529847

theorem tailTrace_1765668 : CollatzResearch.WordTrace tailWord_1765668 prefixEnd_1765668 906636360262903049529847 := by
  unfold tailWord_1765668
  simp only [CollatzResearch.WordTrace]
  refine ⟨32199601283646931465860829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42932801711529241954481105 32199601283646931465860829)
  ·
    refine ⟨12074850481367599299697811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32199601283646931465860829 12074850481367599299697811)
    ·
      refine ⟨18112275722051398949546717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12074850481367599299697811 18112275722051398949546717)
      ·
        refine ⟨6792103395769274606080019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18112275722051398949546717 6792103395769274606080019)
        ·
          refine ⟨10188155093653911909120029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6792103395769274606080019 10188155093653911909120029)
          ·
            refine ⟨3820558160120216965920011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10188155093653911909120029 3820558160120216965920011)
            ·
              refine ⟨5730837240180325448880017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3820558160120216965920011 5730837240180325448880017)
              ·
                refine ⟨4298127930135244086660013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5730837240180325448880017 4298127930135244086660013)
                ·
                  refine ⟨1611797973800716532497505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4298127930135244086660013 1611797973800716532497505)
                  ·
                    refine ⟨1208848480350537399373129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1611797973800716532497505 1208848480350537399373129)
                    ·
                      refine ⟨906636360262903049529847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1208848480350537399373129 906636360262903049529847)
                      ·
                        rfl

theorem cell23_1765668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_1765668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765668 prefixEnd_1765668 := by exact prefixLift 1765668
  have htrace : WordTrace (prefixWord ++ tailWord_1765668) baseStart_1765668 baseEnd_1765668 := by
    simpa [prefixWord, tailWord_1765668, baseEnd_1765668] using wordTrace_append hprefix tailTrace_1765668
  have hstable : (prefixWord ++ tailWord_1765668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765668).length < 2 ^ (prefixWord ++ tailWord_1765668).sum := by decide
  have hdescent : baseEnd_1765668 < baseStart_1765668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765685 : List Nat := [1, 3, 3, 1, 2, 1, 4, 3, 1, 2, 2]
def baseStart_1765685 : Nat := 118140960795 + 1765685 * 2 ^ 59
def prefixEnd_1765685 : Nat := 4983230072969 + 3 ^ 40 * 1765685 * 2
def baseEnd_1765685 : Nat := 906645089434029483017269

theorem tailTrace_1765685 : CollatzResearch.WordTrace tailWord_1765685 prefixEnd_1765685 906645089434029483017269 := by
  unfold tailWord_1765685
  simp only [CollatzResearch.WordTrace]
  refine ⟨64399822608232274835090509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42933215072154849890060339 64399822608232274835090509)
  ·
    refine ⟨24149933478087103063158941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64399822608232274835090509 24149933478087103063158941)
    ·
      refine ⟨9056225054282663648684603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24149933478087103063158941 9056225054282663648684603)
      ·
        refine ⟨13584337581423995473026905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9056225054282663648684603 13584337581423995473026905)
        ·
          refine ⟨10188253186067996604770179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13584337581423995473026905 10188253186067996604770179)
          ·
            refine ⟨15282379779101994907155269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10188253186067996604770179 15282379779101994907155269)
            ·
              refine ⟨2865446208581624045091613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15282379779101994907155269 2865446208581624045091613)
              ·
                refine ⟨1074542328218109016909355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2865446208581624045091613 1074542328218109016909355)
                ·
                  refine ⟨1611813492327163525364033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1074542328218109016909355 1611813492327163525364033)
                  ·
                    refine ⟨1208860119245372644023025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1611813492327163525364033 1208860119245372644023025)
                    ·
                      refine ⟨906645089434029483017269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1208860119245372644023025 906645089434029483017269)
                      ·
                        rfl

theorem cell23_1765685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_1765685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765685 prefixEnd_1765685 := by exact prefixLift 1765685
  have htrace : WordTrace (prefixWord ++ tailWord_1765685) baseStart_1765685 baseEnd_1765685 := by
    simpa [prefixWord, tailWord_1765685, baseEnd_1765685] using wordTrace_append hprefix tailTrace_1765685
  have hstable : (prefixWord ++ tailWord_1765685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765685).length < 2 ^ (prefixWord ++ tailWord_1765685).sum := by decide
  have hdescent : baseEnd_1765685 < baseStart_1765685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765707 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 4]
def baseStart_1765707 : Nat := 118140960795 + 1765707 * 2 ^ 59
def prefixEnd_1765707 : Nat := 4983230072969 + 3 ^ 40 * 1765707 * 2
def baseEnd_1765707 : Nat := 906656386008428396942167

theorem tailTrace_1765707 : CollatzResearch.WordTrace tailWord_1765707 prefixEnd_1765707 906656386008428396942167 := by
  unfold tailWord_1765707
  simp only [CollatzResearch.WordTrace]
  refine ⟨64400625014152572592391375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42933750009435048394927583 64400625014152572592391375)
  ·
    refine ⟨96600937521228858888587063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64400625014152572592391375 96600937521228858888587063)
    ·
      refine ⟨144901406281843288332880595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96600937521228858888587063 144901406281843288332880595)
      ·
        refine ⟨217352109422764932499320893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144901406281843288332880595 217352109422764932499320893)
        ·
          refine ⟨81507041033536849687245335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217352109422764932499320893 81507041033536849687245335)
          ·
            refine ⟨122260561550305274530868003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81507041033536849687245335 122260561550305274530868003)
            ·
              refine ⟨183390842325457911796302005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122260561550305274530868003 183390842325457911796302005)
              ·
                refine ⟨17192891468011679230903313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 183390842325457911796302005 17192891468011679230903313)
                ·
                  refine ⟨12894668601008759423177485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17192891468011679230903313 12894668601008759423177485)
                  ·
                    refine ⟨4835500725378284783691557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12894668601008759423177485 4835500725378284783691557)
                    ·
                      refine ⟨906656386008428396942167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4835500725378284783691557 906656386008428396942167)
                      ·
                        rfl

theorem cell23_1765707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 4].length) (baseStart_1765707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765707 prefixEnd_1765707 := by exact prefixLift 1765707
  have htrace : WordTrace (prefixWord ++ tailWord_1765707) baseStart_1765707 baseEnd_1765707 := by
    simpa [prefixWord, tailWord_1765707, baseEnd_1765707] using wordTrace_append hprefix tailTrace_1765707
  have hstable : (prefixWord ++ tailWord_1765707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765707).length < 2 ^ (prefixWord ++ tailWord_1765707).sum := by decide
  have hdescent : baseEnd_1765707 < baseStart_1765707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765741 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 3, 4, 2]
def baseStart_1765741 : Nat := 118140960795 + 1765741 * 2 ^ 59
def prefixEnd_1765741 : Nat := 4983230072969 + 3 ^ 40 * 1765741 * 2
def baseEnd_1765741 : Nat := 906673844350681263917011

theorem tailTrace_1765741 : CollatzResearch.WordTrace tailWord_1765741 prefixEnd_1765741 906673844350681263917011 := by
  unfold tailWord_1765741
  simp only [CollatzResearch.WordTrace]
  refine ⟨64401865096029396399129077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42934576730686264266086051 64401865096029396399129077)
  ·
    refine ⟨6037674852752755912418351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64401865096029396399129077 6037674852752755912418351)
    ·
      refine ⟨9056512279129133868627527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6037674852752755912418351 9056512279129133868627527)
      ·
        refine ⟨13584768418693700802941291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9056512279129133868627527 13584768418693700802941291)
        ·
          refine ⟨20377152628040551204411937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13584768418693700802941291 20377152628040551204411937)
          ·
            refine ⟨15282864471030413403308953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20377152628040551204411937 15282864471030413403308953)
            ·
              refine ⟨11462148353272810052481715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15282864471030413403308953 11462148353272810052481715)
              ·
                refine ⟨17193222529909215078722573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11462148353272810052481715 17193222529909215078722573)
                ·
                  refine ⟨6447458448715955654520965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17193222529909215078722573 6447458448715955654520965)
                  ·
                    refine ⟨1208898459134241685222681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6447458448715955654520965 1208898459134241685222681)
                    ·
                      refine ⟨906673844350681263917011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1208898459134241685222681 906673844350681263917011)
                      ·
                        rfl

theorem cell23_1765741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_1765741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765741 prefixEnd_1765741 := by exact prefixLift 1765741
  have htrace : WordTrace (prefixWord ++ tailWord_1765741) baseStart_1765741 baseEnd_1765741 := by
    simpa [prefixWord, tailWord_1765741, baseEnd_1765741] using wordTrace_append hprefix tailTrace_1765741
  have hstable : (prefixWord ++ tailWord_1765741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765741).length < 2 ^ (prefixWord ++ tailWord_1765741).sum := by decide
  have hdescent : baseEnd_1765741 < baseStart_1765741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765744 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 5]
def baseStart_1765744 : Nat := 118140960795 + 1765744 * 2 ^ 59
def prefixEnd_1765744 : Nat := 4983230072969 + 3 ^ 40 * 1765744 * 2
def baseEnd_1765744 : Nat := 906675384792644752179497

theorem tailTrace_1765744 : CollatzResearch.WordTrace tailWord_1765744 prefixEnd_1765744 906675384792644752179497 := by
  unfold tailWord_1765744
  simp only [CollatzResearch.WordTrace]
  refine ⟨32200987257509263955744143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42934649676679018607658857 32200987257509263955744143)
  ·
    refine ⟨48301480886263895933616215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32200987257509263955744143 48301480886263895933616215)
    ·
      refine ⟨72452221329395843900424323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48301480886263895933616215 72452221329395843900424323)
      ·
        refine ⟨108678331994093765850636485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72452221329395843900424323 108678331994093765850636485)
        ·
          refine ⟨20377187248892581096994341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108678331994093765850636485 20377187248892581096994341)
          ·
            refine ⟨3820722609167358955686439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20377187248892581096994341 3820722609167358955686439)
            ·
              refine ⟨5731083913751038433529659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3820722609167358955686439 5731083913751038433529659)
              ·
                refine ⟨8596625870626557650294489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5731083913751038433529659 8596625870626557650294489)
                ·
                  refine ⟨6447469402969918237720867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8596625870626557650294489 6447469402969918237720867)
                  ·
                    refine ⟨9671204104454877356581301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6447469402969918237720867 9671204104454877356581301)
                    ·
                      refine ⟨906675384792644752179497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9671204104454877356581301 906675384792644752179497)
                      ·
                        rfl

theorem cell23_1765744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 5].length) (baseStart_1765744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765744 prefixEnd_1765744 := by exact prefixLift 1765744
  have htrace : WordTrace (prefixWord ++ tailWord_1765744) baseStart_1765744 baseEnd_1765744 := by
    simpa [prefixWord, tailWord_1765744, baseEnd_1765744] using wordTrace_append hprefix tailTrace_1765744
  have hstable : (prefixWord ++ tailWord_1765744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765744).length < 2 ^ (prefixWord ++ tailWord_1765744).sum := by decide
  have hdescent : baseEnd_1765744 < baseStart_1765744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765831 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 1, 6, 2]
def baseStart_1765831 : Nat := 118140960795 + 1765831 * 2 ^ 59
def prefixEnd_1765831 : Nat := 4983230072969 + 3 ^ 40 * 1765831 * 2
def baseEnd_1765831 : Nat := 906720057609585911791597

theorem tailTrace_1765831 : CollatzResearch.WordTrace tailWord_1765831 prefixEnd_1765831 906720057609585911791597 := by
  unfold tailWord_1765831
  simp only [CollatzResearch.WordTrace]
  refine ⟨64405147665703341769905347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42936765110468894513270231 64405147665703341769905347)
  ·
    refine ⟨96607721498555012654858021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64405147665703341769905347 96607721498555012654858021)
    ·
      refine ⟨18113947780979064872785879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96607721498555012654858021 18113947780979064872785879)
      ·
        refine ⟨27170921671468597309178819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18113947780979064872785879 27170921671468597309178819)
        ·
          refine ⟨40756382507202895963768229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27170921671468597309178819 40756382507202895963768229)
          ·
            refine ⟨7641821720100542993206543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40756382507202895963768229 7641821720100542993206543)
            ·
              refine ⟨11462732580150814489809815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7641821720100542993206543 11462732580150814489809815)
              ·
                refine ⟨17194098870226221734714723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11462732580150814489809815 17194098870226221734714723)
                ·
                  refine ⟨25791148305339332602072085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17194098870226221734714723 25791148305339332602072085)
                  ·
                    refine ⟨1208960076812781215722129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25791148305339332602072085 1208960076812781215722129)
                    ·
                      refine ⟨906720057609585911791597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1208960076812781215722129 906720057609585911791597)
                      ·
                        rfl

theorem cell23_1765831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_1765831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765831 prefixEnd_1765831 := by exact prefixLift 1765831
  have htrace : WordTrace (prefixWord ++ tailWord_1765831) baseStart_1765831 baseEnd_1765831 := by
    simpa [prefixWord, tailWord_1765831, baseEnd_1765831] using wordTrace_append hprefix tailTrace_1765831
  have hstable : (prefixWord ++ tailWord_1765831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765831).length < 2 ^ (prefixWord ++ tailWord_1765831).sum := by decide
  have hdescent : baseEnd_1765831 < baseStart_1765831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765891 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 3, 5, 2]
def baseStart_1765891 : Nat := 118140960795 + 1765891 * 2 ^ 59
def prefixEnd_1765891 : Nat := 4983230072969 + 3 ^ 40 * 1765891 * 2
def baseEnd_1765891 : Nat := 906750866448855677041321

theorem tailTrace_1765891 : CollatzResearch.WordTrace tailWord_1765891 prefixEnd_1765891 906750866448855677041321 := by
  unfold tailWord_1765891
  simp only [CollatzResearch.WordTrace]
  refine ⟨64407336045485972017089527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42938224030323981344726351 64407336045485972017089527)
  ·
    refine ⟨96611004068228958025634291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64407336045485972017089527 96611004068228958025634291)
    ·
      refine ⟨144916506102343437038451437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96611004068228958025634291 144916506102343437038451437)
      ·
        refine ⟨54343689788378788889419289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144916506102343437038451437 54343689788378788889419289)
        ·
          refine ⟨40757767341284091667064467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54343689788378788889419289 40757767341284091667064467)
          ·
            refine ⟨61136651011926137500596701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40757767341284091667064467 61136651011926137500596701)
            ·
              refine ⟨22926244129472301562723763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61136651011926137500596701 22926244129472301562723763)
              ·
                refine ⟨34389366194208452344085645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22926244129472301562723763 34389366194208452344085645)
                ·
                  refine ⟨12896012322828169629032117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34389366194208452344085645 12896012322828169629032117)
                  ·
                    refine ⟨1209001155265140902721761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12896012322828169629032117 1209001155265140902721761)
                    ·
                      refine ⟨906750866448855677041321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1209001155265140902721761 906750866448855677041321)
                      ·
                        rfl

theorem cell23_1765891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 5, 2].length) (baseStart_1765891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765891 prefixEnd_1765891 := by exact prefixLift 1765891
  have htrace : WordTrace (prefixWord ++ tailWord_1765891) baseStart_1765891 baseEnd_1765891 := by
    simpa [prefixWord, tailWord_1765891, baseEnd_1765891] using wordTrace_append hprefix tailTrace_1765891
  have hstable : (prefixWord ++ tailWord_1765891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765891).length < 2 ^ (prefixWord ++ tailWord_1765891).sum := by decide
  have hdescent : baseEnd_1765891 < baseStart_1765891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765898 : List Nat := [3, 1, 2, 2, 2, 1, 1, 4, 3, 1, 3]
def baseStart_1765898 : Nat := 118140960795 + 1765898 * 2 ^ 59
def prefixEnd_1765898 : Nat := 4983230072969 + 3 ^ 40 * 1765898 * 2
def baseEnd_1765898 : Nat := 906754460813437149653789

theorem tailTrace_1765898 : CollatzResearch.WordTrace tailWord_1765898 prefixEnd_1765898 906754460813437149653789 := by
  unfold tailWord_1765898
  simp only [CollatzResearch.WordTrace]
  refine ⟨16101897839115153053148587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42938394237640408141729565 16101897839115153053148587)
  ·
    refine ⟨24152846758672729579722881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16101897839115153053148587 24152846758672729579722881)
    ·
      refine ⟨18114635069004547184792161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24152846758672729579722881 18114635069004547184792161)
      ·
        refine ⟨13585976301753410388594121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18114635069004547184792161 13585976301753410388594121)
        ·
          refine ⟨10189482226315057791445591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13585976301753410388594121 10189482226315057791445591)
          ·
            refine ⟨15284223339472586687168387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10189482226315057791445591 15284223339472586687168387)
            ·
              refine ⟨22926335009208880030752581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15284223339472586687168387 22926335009208880030752581)
              ·
                refine ⟨4298687814226665005766109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22926335009208880030752581 4298687814226665005766109)
                ·
                  refine ⟨1612007930334999377162291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4298687814226665005766109 1612007930334999377162291)
                  ·
                    refine ⟨2418011895502499065743437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1612007930334999377162291 2418011895502499065743437)
                    ·
                      refine ⟨906754460813437149653789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2418011895502499065743437 906754460813437149653789)
                      ·
                        rfl

theorem cell23_1765898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_1765898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765898 prefixEnd_1765898 := by exact prefixLift 1765898
  have htrace : WordTrace (prefixWord ++ tailWord_1765898) baseStart_1765898 baseEnd_1765898 := by
    simpa [prefixWord, tailWord_1765898, baseEnd_1765898] using wordTrace_append hprefix tailTrace_1765898
  have hstable : (prefixWord ++ tailWord_1765898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765898).length < 2 ^ (prefixWord ++ tailWord_1765898).sum := by decide
  have hdescent : baseEnd_1765898 < baseStart_1765898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765941 : List Nat := [1, 3, 3, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_1765941 : Nat := 118140960795 + 1765941 * 2 ^ 59
def prefixEnd_1765941 : Nat := 4983230072969 + 3 ^ 40 * 1765941 * 2
def baseEnd_1765941 : Nat := 906776540481580481416091

theorem tailTrace_1765941 : CollatzResearch.WordTrace tailWord_1765941 prefixEnd_1765941 906776540481580481416091 := by
  unfold tailWord_1765941
  simp only [CollatzResearch.WordTrace]
  refine ⟨64409159695304830556409677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42939439796869887037606451 64409159695304830556409677)
  ·
    refine ⟨24153434885739311458653629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64409159695304830556409677 24153434885739311458653629)
    ·
      refine ⟨9057538082152241796995111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24153434885739311458653629 9057538082152241796995111)
      ·
        refine ⟨13586307123228362695492667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9057538082152241796995111 13586307123228362695492667)
        ·
          refine ⟨20379460684842544043239001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13586307123228362695492667 20379460684842544043239001)
          ·
            refine ⟨15284595513631908032429251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20379460684842544043239001 15284595513631908032429251)
            ·
              refine ⟨22926893270447862048643877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15284595513631908032429251 22926893270447862048643877)
              ·
                refine ⟨4298792488208974134120727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22926893270447862048643877 4298792488208974134120727)
                ·
                  refine ⟨6448188732313461201181091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4298792488208974134120727 6448188732313461201181091)
                  ·
                    refine ⟨9672283098470191801771637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6448188732313461201181091 9672283098470191801771637)
                    ·
                      refine ⟨906776540481580481416091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9672283098470191801771637 906776540481580481416091)
                      ·
                        rfl

theorem cell23_1765941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_1765941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765941 prefixEnd_1765941 := by exact prefixLift 1765941
  have htrace : WordTrace (prefixWord ++ tailWord_1765941) baseStart_1765941 baseEnd_1765941 := by
    simpa [prefixWord, tailWord_1765941, baseEnd_1765941] using wordTrace_append hprefix tailTrace_1765941
  have hstable : (prefixWord ++ tailWord_1765941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765941).length < 2 ^ (prefixWord ++ tailWord_1765941).sum := by decide
  have hdescent : baseEnd_1765941 < baseStart_1765941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765951 : List Nat := [1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 4]
def baseStart_1765951 : Nat := 118140960795 + 1765951 * 2 ^ 59
def prefixEnd_1765951 : Nat := 4983230072969 + 3 ^ 40 * 1765951 * 2
def baseEnd_1765951 : Nat := 906781675288125442291045

theorem tailTrace_1765951 : CollatzResearch.WordTrace tailWord_1765951 prefixEnd_1765951 906781675288125442291045 := by
  unfold tailWord_1765951
  simp only [CollatzResearch.WordTrace]
  refine ⟨64409524425268602264273707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42939682950179068176182471 64409524425268602264273707)
  ·
    refine ⟨96614286637902903396410561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64409524425268602264273707 96614286637902903396410561)
    ·
      refine ⟨72460714978427177547307921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96614286637902903396410561 72460714978427177547307921)
      ·
        refine ⟨54345536233820383160480941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72460714978427177547307921 54345536233820383160480941)
        ·
          refine ⟨20379576087682643685180353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54345536233820383160480941 20379576087682643685180353)
          ·
            refine ⟨15284682065761982763885265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20379576087682643685180353 15284682065761982763885265)
            ·
              refine ⟨11463511549321487072913949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15284682065761982763885265 11463511549321487072913949)
              ·
                refine ⟨4298816830995557652342731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11463511549321487072913949 4298816830995557652342731)
                ·
                  refine ⟨6448225246493336478514097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4298816830995557652342731 6448225246493336478514097)
                  ·
                    refine ⟨4836168934870002358885573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6448225246493336478514097 4836168934870002358885573)
                    ·
                      refine ⟨906781675288125442291045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4836168934870002358885573 906781675288125442291045)
                      ·
                        rfl

theorem cell23_1765951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_1765951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765951 prefixEnd_1765951 := by exact prefixLift 1765951
  have htrace : WordTrace (prefixWord ++ tailWord_1765951) baseStart_1765951 baseEnd_1765951 := by
    simpa [prefixWord, tailWord_1765951, baseEnd_1765951] using wordTrace_append hprefix tailTrace_1765951
  have hstable : (prefixWord ++ tailWord_1765951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765951).length < 2 ^ (prefixWord ++ tailWord_1765951).sum := by decide
  have hdescent : baseEnd_1765951 < baseStart_1765951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765975 : List Nat := [1, 1, 3, 2, 2, 2, 5, 1, 1, 2, 3]
def baseStart_1765975 : Nat := 118140960795 + 1765975 * 2 ^ 59
def prefixEnd_1765975 : Nat := 4983230072969 + 3 ^ 40 * 1765975 * 2
def baseEnd_1765975 : Nat := 906793998823833348390935

theorem tailTrace_1765975 : CollatzResearch.WordTrace tailWord_1765975 prefixEnd_1765975 906793998823833348390935 := by
  unfold tailWord_1765975
  simp only [CollatzResearch.WordTrace]
  refine ⟨64410399777181654363147379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42940266518121102908764919 64410399777181654363147379)
  ·
    refine ⟨96615599665772481544721069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64410399777181654363147379 96615599665772481544721069)
    ·
      refine ⟨36230849874664680579270401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96615599665772481544721069 36230849874664680579270401)
      ·
        refine ⟨27173137405998510434452801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36230849874664680579270401 27173137405998510434452801)
        ·
          refine ⟨20379853054498882825839601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27173137405998510434452801 20379853054498882825839601)
          ·
            refine ⟨15284889790874162119379701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20379853054498882825839601 15284889790874162119379701)
            ·
              refine ⟨1432958417894452698691847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15284889790874162119379701 1432958417894452698691847)
              ·
                refine ⟨2149437626841679048037771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432958417894452698691847 2149437626841679048037771)
                ·
                  refine ⟨3224156440262518572056657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2149437626841679048037771 3224156440262518572056657)
                  ·
                    refine ⟨2418117330196888929042493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3224156440262518572056657 2418117330196888929042493)
                    ·
                      refine ⟨906793998823833348390935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2418117330196888929042493 906793998823833348390935)
                      ·
                        rfl

theorem cell23_1765975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_1765975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765975 prefixEnd_1765975 := by exact prefixLift 1765975
  have htrace : WordTrace (prefixWord ++ tailWord_1765975) baseStart_1765975 baseEnd_1765975 := by
    simpa [prefixWord, tailWord_1765975, baseEnd_1765975] using wordTrace_append hprefix tailTrace_1765975
  have hstable : (prefixWord ++ tailWord_1765975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765975).length < 2 ^ (prefixWord ++ tailWord_1765975).sum := by decide
  have hdescent : baseEnd_1765975 < baseStart_1765975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765989 : List Nat := [1, 3, 1, 3, 4, 1, 1, 4, 1, 2, 2]
def baseStart_1765989 : Nat := 118140960795 + 1765989 * 2 ^ 59
def prefixEnd_1765989 : Nat := 4983230072969 + 3 ^ 40 * 1765989 * 2
def baseEnd_1765989 : Nat := 906801187552996293615871

theorem tailTrace_1765989 : CollatzResearch.WordTrace tailWord_1765989 prefixEnd_1765989 906801187552996293615871 := by
  unfold tailWord_1765989
  simp only [CollatzResearch.WordTrace]
  refine ⟨64410910399130934754157021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42940606932753956502771347 64410910399130934754157021)
  ·
    refine ⟨24154091399674100532808883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64410910399130934754157021 24154091399674100532808883)
    ·
      refine ⟨36231137099511150799213325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24154091399674100532808883 36231137099511150799213325)
      ·
        refine ⟨13586676412316681549704997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36231137099511150799213325 13586676412316681549704997)
        ·
          refine ⟨2547501827309377790569687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13586676412316681549704997 2547501827309377790569687)
          ·
            refine ⟨3821252740964066685854531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2547501827309377790569687 3821252740964066685854531)
            ·
              refine ⟨5731879111446100028781797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3821252740964066685854531 5731879111446100028781797)
              ·
                refine ⟨1074727333396143755396587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5731879111446100028781797 1074727333396143755396587)
                ·
                  refine ⟨1612091000094215633094881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1074727333396143755396587 1612091000094215633094881)
                  ·
                    refine ⟨1209068250070661724821161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1612091000094215633094881 1209068250070661724821161)
                    ·
                      refine ⟨906801187552996293615871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1209068250070661724821161 906801187552996293615871)
                      ·
                        rfl

theorem cell23_1765989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_1765989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1765989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1765989 prefixEnd_1765989 := by exact prefixLift 1765989
  have htrace : WordTrace (prefixWord ++ tailWord_1765989) baseStart_1765989 baseEnd_1765989 := by
    simpa [prefixWord, tailWord_1765989, baseEnd_1765989] using wordTrace_append hprefix tailTrace_1765989
  have hstable : (prefixWord ++ tailWord_1765989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765989).length < 2 ^ (prefixWord ++ tailWord_1765989).sum := by decide
  have hdescent : baseEnd_1765989 < baseStart_1765989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766028 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 3, 4, 2]
def baseStart_1766028 : Nat := 118140960795 + 1766028 * 2 ^ 59
def prefixEnd_1766028 : Nat := 4983230072969 + 3 ^ 40 * 1766028 * 2
def baseEnd_1766028 : Nat := 906821213298521641028191

theorem tailTrace_1766028 : CollatzResearch.WordTrace tailWord_1766028 prefixEnd_1766028 906821213298521641028191 := by
  unfold tailWord_1766028
  simp only [CollatzResearch.WordTrace]
  refine ⟨32206166422994822207413369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42941555230659762943217825 32206166422994822207413369)
  ·
    refine ⟨24154624817246116655560027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32206166422994822207413369 24154624817246116655560027)
    ·
      refine ⟨36231937225869174983340041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24154624817246116655560027 36231937225869174983340041)
      ·
        refine ⟨27173952919401881237505031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36231937225869174983340041 27173952919401881237505031)
        ·
          refine ⟨40760929379102821856257547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27173952919401881237505031 40760929379102821856257547)
          ·
            refine ⟨61141394068654232784386321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40760929379102821856257547 61141394068654232784386321)
            ·
              refine ⟨45856045551490674588289741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61141394068654232784386321 45856045551490674588289741)
              ·
                refine ⟨17196017081809002970608653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45856045551490674588289741 17196017081809002970608653)
                ·
                  refine ⟨6448506405678376113978245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17196017081809002970608653 6448506405678376113978245)
                  ·
                    refine ⟨1209094951064695521370921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6448506405678376113978245 1209094951064695521370921)
                    ·
                      refine ⟨906821213298521641028191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1209094951064695521370921 906821213298521641028191)
                      ·
                        rfl

theorem cell23_1766028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_1766028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766028 prefixEnd_1766028 := by exact prefixLift 1766028
  have htrace : WordTrace (prefixWord ++ tailWord_1766028) baseStart_1766028 baseEnd_1766028 := by
    simpa [prefixWord, tailWord_1766028, baseEnd_1766028] using wordTrace_append hprefix tailTrace_1766028
  have hstable : (prefixWord ++ tailWord_1766028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766028).length < 2 ^ (prefixWord ++ tailWord_1766028).sum := by decide
  have hdescent : baseEnd_1766028 < baseStart_1766028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766031 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 3]
def baseStart_1766031 : Nat := 118140960795 + 1766031 * 2 ^ 59
def prefixEnd_1766031 : Nat := 4983230072969 + 3 ^ 40 * 1766031 * 2
def baseEnd_1766031 : Nat := 906822753740485129290677

theorem tailTrace_1766031 : CollatzResearch.WordTrace tailWord_1766031 prefixEnd_1766031 906822753740485129290677 := by
  unfold tailWord_1766031
  simp only [CollatzResearch.WordTrace]
  refine ⟨64412442264978775927185947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42941628176652517284790631 64412442264978775927185947)
  ·
    refine ⟨96618663397468163890778921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64412442264978775927185947 96618663397468163890778921)
    ·
      refine ⟨72463997548101122918084191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96618663397468163890778921 72463997548101122918084191)
      ·
        refine ⟨108695996322151684377126287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72463997548101122918084191 108695996322151684377126287)
        ·
          refine ⟨163043994483227526565689431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108695996322151684377126287 163043994483227526565689431)
          ·
            refine ⟨244565991724841289848534147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163043994483227526565689431 244565991724841289848534147)
            ·
              refine ⟨366848987587261934772801221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244565991724841289848534147 366848987587261934772801221)
              ·
                refine ⟨68784185172611612769900229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 366848987587261934772801221 68784185172611612769900229)
                ·
                  refine ⟨12897034719864677394356293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68784185172611612769900229 12897034719864677394356293)
                  ·
                    refine ⟨2418194009974627011441805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12897034719864677394356293 2418194009974627011441805)
                    ·
                      refine ⟨906822753740485129290677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2418194009974627011441805 906822753740485129290677)
                      ·
                        rfl

theorem cell23_1766031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 3].length) (baseStart_1766031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766031 prefixEnd_1766031 := by exact prefixLift 1766031
  have htrace : WordTrace (prefixWord ++ tailWord_1766031) baseStart_1766031 baseEnd_1766031 := by
    simpa [prefixWord, tailWord_1766031, baseEnd_1766031] using wordTrace_append hprefix tailTrace_1766031
  have hstable : (prefixWord ++ tailWord_1766031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766031).length < 2 ^ (prefixWord ++ tailWord_1766031).sum := by decide
  have hdescent : baseEnd_1766031 < baseStart_1766031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766041 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 4, 2, 4]
def baseStart_1766041 : Nat := 118140960795 + 1766041 * 2 ^ 59
def prefixEnd_1766041 : Nat := 4983230072969 + 3 ^ 40 * 1766041 * 2
def baseEnd_1766041 : Nat := 906827888547030090165631

theorem tailTrace_1766041 : CollatzResearch.WordTrace tailWord_1766041 prefixEnd_1766041 906827888547030090165631 := by
  unfold tailWord_1766041
  simp only [CollatzResearch.WordTrace]
  refine ⟨64412806994942547635049977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42941871329961698423366651 64412806994942547635049977)
  ·
    refine ⟨48309605246206910726287483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64412806994942547635049977 48309605246206910726287483)
    ·
      refine ⟨72464407869310366089431225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48309605246206910726287483 72464407869310366089431225)
      ·
        refine ⟨54348305901982774567073419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72464407869310366089431225 54348305901982774567073419)
        ·
          refine ⟨81522458852974161850610129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54348305901982774567073419 81522458852974161850610129)
          ·
            refine ⟨61141844139730621387957597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81522458852974161850610129 61141844139730621387957597)
            ·
              refine ⟨22928191552398983020484099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61141844139730621387957597 22928191552398983020484099)
              ·
                refine ⟨34392287328598474530726149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22928191552398983020484099 34392287328598474530726149)
                ·
                  refine ⟨6448553874112213974511153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34392287328598474530726149 6448553874112213974511153)
                  ·
                    refine ⟨4836415405584160480883365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6448553874112213974511153 4836415405584160480883365)
                    ·
                      refine ⟨906827888547030090165631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4836415405584160480883365 906827888547030090165631)
                      ·
                        rfl

theorem cell23_1766041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_1766041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766041 prefixEnd_1766041 := by exact prefixLift 1766041
  have htrace : WordTrace (prefixWord ++ tailWord_1766041) baseStart_1766041 baseEnd_1766041 := by
    simpa [prefixWord, tailWord_1766041, baseEnd_1766041] using wordTrace_append hprefix tailTrace_1766041
  have hstable : (prefixWord ++ tailWord_1766041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766041).length < 2 ^ (prefixWord ++ tailWord_1766041).sum := by decide
  have hdescent : baseEnd_1766041 < baseStart_1766041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766128 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 5, 4]
def baseStart_1766128 : Nat := 118140960795 + 1766128 * 2 ^ 59
def prefixEnd_1766128 : Nat := 4983230072969 + 3 ^ 40 * 1766128 * 2
def baseEnd_1766128 : Nat := 302290853787990416592577

theorem tailTrace_1766128 : CollatzResearch.WordTrace tailWord_1766128 prefixEnd_1766128 302290853787990416592577 := by
  unfold tailWord_1766128
  simp only [CollatzResearch.WordTrace]
  refine ⟨32207990072813680746733519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42943986763751574328978025 32207990072813680746733519)
  ·
    refine ⟨48311985109220521120100279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32207990072813680746733519 48311985109220521120100279)
    ·
      refine ⟨72467977663830781680150419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48311985109220521120100279 72467977663830781680150419)
      ·
        refine ⟨108701966495746172520225629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72467977663830781680150419 108701966495746172520225629)
        ·
          refine ⟨40763237435904814695084611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108701966495746172520225629 40763237435904814695084611)
          ·
            refine ⟨61144856153857222042626917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40763237435904814695084611 61144856153857222042626917)
            ·
              refine ⟨11464660528848229132992547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61144856153857222042626917 11464660528848229132992547)
              ·
                refine ⟨17196990793272343699488821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11464660528848229132992547 17196990793272343699488821)
                ·
                  refine ⟨1612217886869282221827077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17196990793272343699488821 1612217886869282221827077)
                  ·
                    refine ⟨302290853787990416592577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1612217886869282221827077 302290853787990416592577)
                    ·
                      rfl

theorem cell23_1766128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 5, 4].length) (baseStart_1766128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766128 prefixEnd_1766128 := by exact prefixLift 1766128
  have htrace : WordTrace (prefixWord ++ tailWord_1766128) baseStart_1766128 baseEnd_1766128 := by
    simpa [prefixWord, tailWord_1766128, baseEnd_1766128] using wordTrace_append hprefix tailTrace_1766128
  have hstable : (prefixWord ++ tailWord_1766128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766128).length < 2 ^ (prefixWord ++ tailWord_1766128).sum := by decide
  have hdescent : baseEnd_1766128 < baseStart_1766128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766131 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 6]
def baseStart_1766131 : Nat := 118140960795 + 1766131 * 2 ^ 59
def prefixEnd_1766131 : Nat := 4983230072969 + 3 ^ 40 * 1766131 * 2
def baseEnd_1766131 : Nat := 906874101805934738040217

theorem tailTrace_1766131 : CollatzResearch.WordTrace tailWord_1766131 prefixEnd_1766131 906874101805934738040217 := by
  unfold tailWord_1766131
  simp only [CollatzResearch.WordTrace]
  refine ⟨64416089564616493005826247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42944059709744328670550831 64416089564616493005826247)
  ·
    refine ⟨96624134346924739508739371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64416089564616493005826247 96624134346924739508739371)
    ·
      refine ⟨144936201520387109263109057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96624134346924739508739371 144936201520387109263109057)
      ·
        refine ⟨108702151140290331947331793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144936201520387109263109057 108702151140290331947331793)
        ·
          refine ⟨81526613355217748960498845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108702151140290331947331793 81526613355217748960498845)
          ·
            refine ⟨30572480008206655860187067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81526613355217748960498845 30572480008206655860187067)
            ·
              refine ⟨45858720012309983790280601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30572480008206655860187067 45858720012309983790280601)
              ·
                refine ⟨34394040009232487842710451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45858720012309983790280601 34394040009232487842710451)
                ·
                  refine ⟨51591060013848731764065677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34394040009232487842710451 51591060013848731764065677)
                  ·
                    refine ⟨19346647505193274411524629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51591060013848731764065677 19346647505193274411524629)
                    ·
                      refine ⟨906874101805934738040217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19346647505193274411524629 906874101805934738040217)
                      ·
                        rfl

theorem cell23_1766131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_1766131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766131 prefixEnd_1766131 := by exact prefixLift 1766131
  have htrace : WordTrace (prefixWord ++ tailWord_1766131) baseStart_1766131 baseEnd_1766131 := by
    simpa [prefixWord, tailWord_1766131, baseEnd_1766131] using wordTrace_append hprefix tailTrace_1766131
  have hstable : (prefixWord ++ tailWord_1766131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766131).length < 2 ^ (prefixWord ++ tailWord_1766131).sum := by decide
  have hdescent : baseEnd_1766131 < baseStart_1766131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766138 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3]
def baseStart_1766138 : Nat := 118140960795 + 1766138 * 2 ^ 59
def prefixEnd_1766138 : Nat := 4983230072969 + 3 ^ 40 * 1766138 * 2
def baseEnd_1766138 : Nat := 906877696170516210652685

theorem tailTrace_1766138 : CollatzResearch.WordTrace tailWord_1766138 prefixEnd_1766138 906877696170516210652685 := by
  unfold tailWord_1766138
  simp only [CollatzResearch.WordTrace]
  refine ⟨16104086218897783300332767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42944229917060755467554045 16104086218897783300332767)
  ·
    refine ⟨24156129328346674950499151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16104086218897783300332767 24156129328346674950499151)
    ·
      refine ⟨36234193992520012425748727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24156129328346674950499151 36234193992520012425748727)
      ·
        refine ⟨54351290988780018638623091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36234193992520012425748727 54351290988780018638623091)
        ·
          refine ⟨81526936483170027957934637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54351290988780018638623091 81526936483170027957934637)
          ·
            refine ⟨30572601181188760484225489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81526936483170027957934637 30572601181188760484225489)
            ·
              refine ⟨22929450885891570363169117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30572601181188760484225489 22929450885891570363169117)
              ·
                refine ⟨8598544082209338886188419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22929450885891570363169117 8598544082209338886188419)
                ·
                  refine ⟨12897816123314008329282629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8598544082209338886188419 12897816123314008329282629)
                  ·
                    refine ⟨2418340523121376561740493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12897816123314008329282629 2418340523121376561740493)
                    ·
                      refine ⟨906877696170516210652685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2418340523121376561740493 906877696170516210652685)
                      ·
                        rfl

theorem cell23_1766138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_1766138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766138 prefixEnd_1766138 := by exact prefixLift 1766138
  have htrace : WordTrace (prefixWord ++ tailWord_1766138) baseStart_1766138 baseEnd_1766138 := by
    simpa [prefixWord, tailWord_1766138, baseEnd_1766138] using wordTrace_append hprefix tailTrace_1766138
  have hstable : (prefixWord ++ tailWord_1766138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766138).length < 2 ^ (prefixWord ++ tailWord_1766138).sum := by decide
  have hdescent : baseEnd_1766138 < baseStart_1766138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766148 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_1766148 : Nat := 118140960795 + 1766148 * 2 ^ 59
def prefixEnd_1766148 : Nat := 4983230072969 + 3 ^ 40 * 1766148 * 2
def baseEnd_1766148 : Nat := 906882830977061171527639

theorem tailTrace_1766148 : CollatzResearch.WordTrace tailWord_1766148 prefixEnd_1766148 906882830977061171527639 := by
  unfold tailWord_1766148
  simp only [CollatzResearch.WordTrace]
  refine ⟨32208354802777452454597549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42944473070369936606130065 32208354802777452454597549)
  ·
    refine ⟨12078133051041544670474081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32208354802777452454597549 12078133051041544670474081)
    ·
      refine ⟨9058599788281158502855561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12078133051041544670474081 9058599788281158502855561)
      ·
        refine ⟨6793949841210868877141671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9058599788281158502855561 6793949841210868877141671)
        ·
          refine ⟨10190924761816303315712507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6793949841210868877141671 10190924761816303315712507)
          ·
            refine ⟨15286387142724454973568761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10190924761816303315712507 15286387142724454973568761)
            ·
              refine ⟨11464790357043341230176571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15286387142724454973568761 11464790357043341230176571)
              ·
                refine ⟨17197185535565011845264857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11464790357043341230176571 17197185535565011845264857)
                ·
                  refine ⟨12897889151673758883948643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17197185535565011845264857 12897889151673758883948643)
                  ·
                    refine ⟨19346833727510638325922965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12897889151673758883948643 19346833727510638325922965)
                    ·
                      refine ⟨906882830977061171527639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19346833727510638325922965 906882830977061171527639)
                      ·
                        rfl

theorem cell23_1766148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_1766148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766148 prefixEnd_1766148 := by exact prefixLift 1766148
  have htrace : WordTrace (prefixWord ++ tailWord_1766148) baseStart_1766148 baseEnd_1766148 := by
    simpa [prefixWord, tailWord_1766148, baseEnd_1766148] using wordTrace_append hprefix tailTrace_1766148
  have hstable : (prefixWord ++ tailWord_1766148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766148).length < 2 ^ (prefixWord ++ tailWord_1766148).sum := by decide
  have hdescent : baseEnd_1766148 < baseStart_1766148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766168 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 2, 5, 3]
def baseStart_1766168 : Nat := 118140960795 + 1766168 * 2 ^ 59
def prefixEnd_1766168 : Nat := 4983230072969 + 3 ^ 40 * 1766168 * 2
def baseEnd_1766168 : Nat := 906893100590151093277547

theorem tailTrace_1766168 : CollatzResearch.WordTrace tailWord_1766168 prefixEnd_1766168 906893100590151093277547 := by
  unfold tailWord_1766168
  simp only [CollatzResearch.WordTrace]
  refine ⟨32208719532741224162461579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42944959376988298883282105 32208719532741224162461579)
  ·
    refine ⟨48313079299111836243692369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32208719532741224162461579 48313079299111836243692369)
    ·
      refine ⟨36234809474333877182769277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48313079299111836243692369 36234809474333877182769277)
      ·
        refine ⟨13588053552875203943538479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36234809474333877182769277 13588053552875203943538479)
        ·
          refine ⟨20382080329312805915307719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13588053552875203943538479 20382080329312805915307719)
          ·
            refine ⟨30573120493969208872961579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20382080329312805915307719 30573120493969208872961579)
            ·
              refine ⟨45859680740953813309442369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30573120493969208872961579 45859680740953813309442369)
              ·
                refine ⟨34394760555715359982081777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45859680740953813309442369 34394760555715359982081777)
                ·
                  refine ⟨25796070416786519986561333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34394760555715359982081777 25796070416786519986561333)
                  ·
                    refine ⟨2418381601573736248740125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25796070416786519986561333 2418381601573736248740125)
                    ·
                      refine ⟨906893100590151093277547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2418381601573736248740125 906893100590151093277547)
                      ·
                        rfl

theorem cell23_1766168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_1766168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766168 prefixEnd_1766168 := by exact prefixLift 1766168
  have htrace : WordTrace (prefixWord ++ tailWord_1766168) baseStart_1766168 baseEnd_1766168 := by
    simpa [prefixWord, tailWord_1766168, baseEnd_1766168] using wordTrace_append hprefix tailTrace_1766168
  have hstable : (prefixWord ++ tailWord_1766168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766168).length < 2 ^ (prefixWord ++ tailWord_1766168).sum := by decide
  have hdescent : baseEnd_1766168 < baseStart_1766168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766171 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 1, 11]
def baseStart_1766171 : Nat := 118140960795 + 1766171 * 2 ^ 59
def prefixEnd_1766171 : Nat := 4983230072969 + 3 ^ 40 * 1766171 * 2
def baseEnd_1766171 : Nat := 302298213677371527180011

theorem tailTrace_1766171 : CollatzResearch.WordTrace tailWord_1766171 prefixEnd_1766171 302298213677371527180011 := by
  unfold tailWord_1766171
  simp only [CollatzResearch.WordTrace]
  refine ⟨64417548484471579837282367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42945032322981053224854911 64417548484471579837282367)
  ·
    refine ⟨96626322726707369755923551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64417548484471579837282367 96626322726707369755923551)
    ·
      refine ⟨144939484090061054633885327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96626322726707369755923551 144939484090061054633885327)
      ·
        refine ⟨217409226135091581950827991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144939484090061054633885327 217409226135091581950827991)
        ·
          refine ⟨326113839202637372926241987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217409226135091581950827991 326113839202637372926241987)
          ·
            refine ⟨489170758803956059389362981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326113839202637372926241987 489170758803956059389362981)
            ·
              refine ⟨91719517275741761135505559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 489170758803956059389362981 91719517275741761135505559)
              ·
                refine ⟨137579275913612641703258339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91719517275741761135505559 137579275913612641703258339)
                ·
                  refine ⟨206368913870418962554887509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137579275913612641703258339 206368913870418962554887509)
                  ·
                    refine ⟨302298213677371527180011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 206368913870418962554887509 302298213677371527180011)
                    ·
                      rfl

theorem cell23_1766171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 11].length) (baseStart_1766171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766171 prefixEnd_1766171 := by exact prefixLift 1766171
  have htrace : WordTrace (prefixWord ++ tailWord_1766171) baseStart_1766171 baseEnd_1766171 := by
    simpa [prefixWord, tailWord_1766171, baseEnd_1766171] using wordTrace_append hprefix tailTrace_1766171
  have hstable : (prefixWord ++ tailWord_1766171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766171).length < 2 ^ (prefixWord ++ tailWord_1766171).sum := by decide
  have hdescent : baseEnd_1766171 < baseStart_1766171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766185 : List Nat := [1, 2, 1, 1, 1, 1, 1, 8, 3, 1, 3]
def baseStart_1766185 : Nat := 118140960795 + 1766185 * 2 ^ 59
def prefixEnd_1766185 : Nat := 4983230072969 + 3 ^ 40 * 1766185 * 2
def baseEnd_1766185 : Nat := 906901829761277526764969

theorem tailTrace_1766185 : CollatzResearch.WordTrace tailWord_1766185 prefixEnd_1766185 906901829761277526764969 := by
  unfold tailWord_1766185
  simp only [CollatzResearch.WordTrace]
  refine ⟨64418059106420860228292009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42945372737613906818861339 64418059106420860228292009)
  ·
    refine ⟨48313544329815645171219007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64418059106420860228292009 48313544329815645171219007)
    ·
      refine ⟨72470316494723467756828511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48313544329815645171219007 72470316494723467756828511)
      ·
        refine ⟨108705474742085201635242767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72470316494723467756828511 108705474742085201635242767)
        ·
          refine ⟨163058212113127802452864151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108705474742085201635242767 163058212113127802452864151)
          ·
            refine ⟨244587318169691703679296227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163058212113127802452864151 244587318169691703679296227)
            ·
              refine ⟨366880977254537555518944341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244587318169691703679296227 366880977254537555518944341)
              ·
                refine ⟨4299386452201611978737629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 366880977254537555518944341 4299386452201611978737629)
                ·
                  refine ⟨1612269919575604492026611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4299386452201611978737629 1612269919575604492026611)
                  ·
                    refine ⟨2418404879363406738039917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1612269919575604492026611 2418404879363406738039917)
                    ·
                      refine ⟨906901829761277526764969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2418404879363406738039917 906901829761277526764969)
                      ·
                        rfl

theorem cell23_1766185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 1, 3].length) (baseStart_1766185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766185 prefixEnd_1766185 := by exact prefixLift 1766185
  have htrace : WordTrace (prefixWord ++ tailWord_1766185) baseStart_1766185 baseEnd_1766185 := by
    simpa [prefixWord, tailWord_1766185, baseEnd_1766185] using wordTrace_append hprefix tailTrace_1766185
  have hstable : (prefixWord ++ tailWord_1766185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766185).length < 2 ^ (prefixWord ++ tailWord_1766185).sum := by decide
  have hdescent : baseEnd_1766185 < baseStart_1766185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766186 : List Nat := [3, 1, 4, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_1766186 : Nat := 118140960795 + 1766186 * 2 ^ 59
def prefixEnd_1766186 : Nat := 4983230072969 + 3 ^ 40 * 1766186 * 2
def baseEnd_1766186 : Nat := 906902343241932022852465

theorem tailTrace_1766186 : CollatzResearch.WordTrace tailWord_1766186 prefixEnd_1766186 906902343241932022852465 := by
  unfold tailWord_1766186
  simp only [CollatzResearch.WordTrace]
  refine ⟨16104523894854309349769603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42945397052944824932718941 16104523894854309349769603)
  ·
    refine ⟨24156785842281464024654405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16104523894854309349769603 24156785842281464024654405)
    ·
      refine ⟨4529397345427774504622701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24156785842281464024654405 4529397345427774504622701)
      ·
        refine ⟨1698524004535415439233513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4529397345427774504622701 1698524004535415439233513)
        ·
          refine ⟨1273893003401561579425135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1698524004535415439233513 1273893003401561579425135)
          ·
            refine ⟨1910839505102342369137703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273893003401561579425135 1910839505102342369137703)
            ·
              refine ⟨2866259257653513553706555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1910839505102342369137703 2866259257653513553706555)
              ·
                refine ⟨4299388886480270330559833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2866259257653513553706555 4299388886480270330559833)
                ·
                  refine ⟨3224541664860202747919875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4299388886480270330559833 3224541664860202747919875)
                  ·
                    refine ⟨4836812497290304121879813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3224541664860202747919875 4836812497290304121879813)
                    ·
                      refine ⟨906902343241932022852465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4836812497290304121879813 906902343241932022852465)
                      ·
                        rfl

theorem cell23_1766186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_1766186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766186 prefixEnd_1766186 := by exact prefixLift 1766186
  have htrace : WordTrace (prefixWord ++ tailWord_1766186) baseStart_1766186 baseEnd_1766186 := by
    simpa [prefixWord, tailWord_1766186, baseEnd_1766186] using wordTrace_append hprefix tailTrace_1766186
  have hstable : (prefixWord ++ tailWord_1766186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766186).length < 2 ^ (prefixWord ++ tailWord_1766186).sum := by decide
  have hdescent : baseEnd_1766186 < baseStart_1766186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766188 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 3, 5]
def baseStart_1766188 : Nat := 118140960795 + 1766188 * 2 ^ 59
def prefixEnd_1766188 : Nat := 4983230072969 + 3 ^ 40 * 1766188 * 2
def baseEnd_1766188 : Nat := 302301123401080338342485

theorem tailTrace_1766188 : CollatzResearch.WordTrace tailWord_1766188 prefixEnd_1766188 302301123401080338342485 := by
  unfold tailWord_1766188
  simp only [CollatzResearch.WordTrace]
  refine ⟨32209084262704995870325609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42945445683606661160434145 32209084262704995870325609)
  ·
    refine ⟨24156813197028746902744207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32209084262704995870325609 24156813197028746902744207)
    ·
      refine ⟨36235219795543120354116311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24156813197028746902744207 36235219795543120354116311)
      ·
        refine ⟨54352829693314680531174467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36235219795543120354116311 54352829693314680531174467)
        ·
          refine ⟨81529244539972020796761701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54352829693314680531174467 81529244539972020796761701)
          ·
            refine ⟨15286733351244753899392819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81529244539972020796761701 15286733351244753899392819)
            ·
              refine ⟨22930100026867130849089229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15286733351244753899392819 22930100026867130849089229)
              ·
                refine ⟨8598787510075174068408461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22930100026867130849089229 8598787510075174068408461)
                ·
                  refine ⟨3224545316278190275653173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8598787510075174068408461 3224545316278190275653173)
                  ·
                    refine ⟨302301123401080338342485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3224545316278190275653173 302301123401080338342485)
                    ·
                      rfl

theorem cell23_1766188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_1766188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766188 prefixEnd_1766188 := by exact prefixLift 1766188
  have htrace : WordTrace (prefixWord ++ tailWord_1766188) baseStart_1766188 baseEnd_1766188 := by
    simpa [prefixWord, tailWord_1766188, baseEnd_1766188] using wordTrace_append hprefix tailTrace_1766188
  have hstable : (prefixWord ++ tailWord_1766188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766188).length < 2 ^ (prefixWord ++ tailWord_1766188).sum := by decide
  have hdescent : baseEnd_1766188 < baseStart_1766188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766189 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_1766189 : Nat := 118140960795 + 1766189 * 2 ^ 59
def prefixEnd_1766189 : Nat := 4983230072969 + 3 ^ 40 * 1766189 * 2
def baseEnd_1766189 : Nat := 906903883683895511114951

theorem tailTrace_1766189 : CollatzResearch.WordTrace tailWord_1766189 prefixEnd_1766189 906903883683895511114951 := by
  unfold tailWord_1766189
  simp only [CollatzResearch.WordTrace]
  refine ⟨64418204998406368911437621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42945469998937579274291747 64418204998406368911437621)
  ·
    refine ⟨6039206718600597085447277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64418204998406368911437621 6039206718600597085447277)
    ·
      refine ⟨2264702519475223907042729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6039206718600597085447277 2264702519475223907042729)
      ·
        refine ⟨1698526889606417930282047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2264702519475223907042729 1698526889606417930282047)
        ·
          refine ⟨2547790334409626895423071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1698526889606417930282047 2547790334409626895423071)
          ·
            refine ⟨3821685501614440343134607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2547790334409626895423071 3821685501614440343134607)
            ·
              refine ⟨5732528252421660514701911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3821685501614440343134607 5732528252421660514701911)
              ·
                refine ⟨8598792378632490772052867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5732528252421660514701911 8598792378632490772052867)
                ·
                  refine ⟨12898188567948736158079301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8598792378632490772052867 12898188567948736158079301)
                  ·
                    refine ⟨2418410356490388029639869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12898188567948736158079301 2418410356490388029639869)
                    ·
                      refine ⟨906903883683895511114951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2418410356490388029639869 906903883683895511114951)
                      ·
                        rfl

theorem cell23_1766189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_1766189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766189 prefixEnd_1766189 := by exact prefixLift 1766189
  have htrace : WordTrace (prefixWord ++ tailWord_1766189) baseStart_1766189 baseEnd_1766189 := by
    simpa [prefixWord, tailWord_1766189, baseEnd_1766189] using wordTrace_append hprefix tailTrace_1766189
  have hstable : (prefixWord ++ tailWord_1766189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766189).length < 2 ^ (prefixWord ++ tailWord_1766189).sum := by decide
  have hdescent : baseEnd_1766189 < baseStart_1766189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766196 : List Nat := [2, 5, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_1766196 : Nat := 118140960795 + 1766196 * 2 ^ 59
def prefixEnd_1766196 : Nat := 4983230072969 + 3 ^ 40 * 1766196 * 2
def baseEnd_1766196 : Nat := 302302492682825661242473

theorem tailTrace_1766196 : CollatzResearch.WordTrace tailWord_1766196 prefixEnd_1766196 302302492682825661242473 := by
  unfold tailWord_1766196
  simp only [CollatzResearch.WordTrace]
  refine ⟨32209230154690504553471221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42945640206254006071294961 32209230154690504553471221)
  ·
    refine ⟨3019615327002234801887927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32209230154690504553471221 3019615327002234801887927)
    ·
      refine ⟨4529422990503352202831891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3019615327002234801887927 4529422990503352202831891)
      ·
        refine ⟨6794134485755028304247837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4529422990503352202831891 6794134485755028304247837)
        ·
          refine ⟨2547800432158135614092939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6794134485755028304247837 2547800432158135614092939)
          ·
            refine ⟨3821700648237203421139409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2547800432158135614092939 3821700648237203421139409)
            ·
              refine ⟨2866275486177902565854557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3821700648237203421139409 2866275486177902565854557)
              ·
                refine ⟨1074853307316713462195459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2866275486177902565854557 1074853307316713462195459)
                ·
                  refine ⟨1612279960975070193293189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1074853307316713462195459 1612279960975070193293189)
                  ·
                    refine ⟨302302492682825661242473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1612279960975070193293189 302302492682825661242473)
                    ·
                      rfl

theorem cell23_1766196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_1766196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766196 prefixEnd_1766196 := by exact prefixLift 1766196
  have htrace : WordTrace (prefixWord ++ tailWord_1766196) baseStart_1766196 baseEnd_1766196 := by
    simpa [prefixWord, tailWord_1766196, baseEnd_1766196] using wordTrace_append hprefix tailTrace_1766196
  have hstable : (prefixWord ++ tailWord_1766196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766196).length < 2 ^ (prefixWord ++ tailWord_1766196).sum := by decide
  have hdescent : baseEnd_1766196 < baseStart_1766196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766209 : List Nat := [1, 2, 5, 3, 1, 2, 1, 2, 6]
def baseStart_1766209 : Nat := 118140960795 + 1766209 * 2 ^ 59
def prefixEnd_1766209 : Nat := 4983230072969 + 3 ^ 40 * 1766209 * 2
def baseEnd_1766209 : Nat := 100768239255220603651651

theorem tailTrace_1766209 : CollatzResearch.WordTrace tailWord_1766209 prefixEnd_1766209 100768239255220603651651 := by
  unfold tailWord_1766209
  simp only [CollatzResearch.WordTrace]
  refine ⟨64418934458333912327165681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42945956305555941551443787 64418934458333912327165681)
  ·
    refine ⟨48314200843750434245374261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64418934458333912327165681 48314200843750434245374261)
    ·
      refine ⟨4529456329101603210503837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48314200843750434245374261 4529456329101603210503837)
      ·
        refine ⟨1698546123413101203938939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4529456329101603210503837 1698546123413101203938939)
        ·
          refine ⟨2547819185119651805908409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1698546123413101203938939 2547819185119651805908409)
          ·
            refine ⟨1910864388839738854431307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2547819185119651805908409 1910864388839738854431307)
            ·
              refine ⟨2866296583259608281646961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1910864388839738854431307 2866296583259608281646961)
              ·
                refine ⟨2149722437444706211235221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2866296583259608281646961 2149722437444706211235221)
                ·
                  refine ⟨100768239255220603651651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2149722437444706211235221 100768239255220603651651)
                  ·
                    rfl

theorem cell23_1766209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 6].length) (baseStart_1766209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766209 prefixEnd_1766209 := by exact prefixLift 1766209
  have htrace : WordTrace (prefixWord ++ tailWord_1766209) baseStart_1766209 baseEnd_1766209 := by
    simpa [prefixWord, tailWord_1766209, baseEnd_1766209] using wordTrace_append hprefix tailTrace_1766209
  have hstable : (prefixWord ++ tailWord_1766209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766209).length < 2 ^ (prefixWord ++ tailWord_1766209).sum := by decide
  have hdescent : baseEnd_1766209 < baseStart_1766209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766245 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 3, 2, 3]
def baseStart_1766245 : Nat := 118140960795 + 1766245 * 2 ^ 59
def prefixEnd_1766245 : Nat := 4983230072969 + 3 ^ 40 * 1766245 * 2
def baseEnd_1766245 : Nat := 906932638600547292014693

theorem tailTrace_1766245 : CollatzResearch.WordTrace tailWord_1766245 prefixEnd_1766245 906932638600547292014693 := by
  unfold tailWord_1766245
  simp only [CollatzResearch.WordTrace]
  refine ⟨64420247486203490475476189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42946831657468993650317459 64420247486203490475476189)
  ·
    refine ⟨24157592807326308928303571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64420247486203490475476189 24157592807326308928303571)
    ·
      refine ⟨36236389210989463392455357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24157592807326308928303571 36236389210989463392455357)
      ·
        refine ⟨13588645954121048772170759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36236389210989463392455357 13588645954121048772170759)
        ·
          refine ⟨20382968931181573158256139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13588645954121048772170759 20382968931181573158256139)
          ·
            refine ⟨30574453396772359737384209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20382968931181573158256139 30574453396772359737384209)
            ·
              refine ⟨22930840047579269803038157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30574453396772359737384209 22930840047579269803038157)
              ·
                refine ⟨8599065017842226176139309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22930840047579269803038157 8599065017842226176139309)
                ·
                  refine ⟨3224649381690834816052241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8599065017842226176139309 3224649381690834816052241)
                  ·
                    refine ⟨2418487036268126112039181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3224649381690834816052241 2418487036268126112039181)
                    ·
                      refine ⟨906932638600547292014693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2418487036268126112039181 906932638600547292014693)
                      ·
                        rfl

theorem cell23_1766245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_1766245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766245 prefixEnd_1766245 := by exact prefixLift 1766245
  have htrace : WordTrace (prefixWord ++ tailWord_1766245) baseStart_1766245 baseEnd_1766245 := by
    simpa [prefixWord, tailWord_1766245, baseEnd_1766245] using wordTrace_append hprefix tailTrace_1766245
  have hstable : (prefixWord ++ tailWord_1766245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766245).length < 2 ^ (prefixWord ++ tailWord_1766245).sum := by decide
  have hdescent : baseEnd_1766245 < baseStart_1766245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766262 : List Nat := [5, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1766262 : Nat := 118140960795 + 1766262 * 2 ^ 59
def prefixEnd_1766262 : Nat := 4983230072969 + 3 ^ 40 * 1766262 * 2
def baseEnd_1766262 : Nat := 906941367771673725502115

theorem tailTrace_1766262 : CollatzResearch.WordTrace tailWord_1766262 prefixEnd_1766262 906941367771673725502115 := by
  unfold tailWord_1766262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4026304220446368898677815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42947245018094601585896693 4026304220446368898677815)
  ·
    refine ⟨6039456330669553348016723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4026304220446368898677815 6039456330669553348016723)
    ·
      refine ⟨9059184496004330022025085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6039456330669553348016723 9059184496004330022025085)
      ·
        refine ⟨3397194186001623758259407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9059184496004330022025085 3397194186001623758259407)
        ·
          refine ⟨5095791279002435637389111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3397194186001623758259407 5095791279002435637389111)
          ·
            refine ⟨7643686918503653456083667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5095791279002435637389111 7643686918503653456083667)
            ·
              refine ⟨11465530377755480184125501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7643686918503653456083667 11465530377755480184125501)
              ·
                refine ⟨4299573891658305069047063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11465530377755480184125501 4299573891658305069047063)
                ·
                  refine ⟨6449360837487457603570595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4299573891658305069047063 6449360837487457603570595)
                  ·
                    refine ⟨9674041256231186405355893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6449360837487457603570595 9674041256231186405355893)
                    ·
                      refine ⟨906941367771673725502115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9674041256231186405355893 906941367771673725502115)
                      ·
                        rfl

theorem cell23_1766262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1766262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766262 prefixEnd_1766262 := by exact prefixLift 1766262
  have htrace : WordTrace (prefixWord ++ tailWord_1766262) baseStart_1766262 baseEnd_1766262 := by
    simpa [prefixWord, tailWord_1766262, baseEnd_1766262] using wordTrace_append hprefix tailTrace_1766262
  have hstable : (prefixWord ++ tailWord_1766262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766262).length < 2 ^ (prefixWord ++ tailWord_1766262).sum := by decide
  have hdescent : baseEnd_1766262 < baseStart_1766262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766270 : List Nat := [4, 2, 3, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_1766270 : Nat := 118140960795 + 1766270 * 2 ^ 59
def prefixEnd_1766270 : Nat := 4983230072969 + 3 ^ 40 * 1766270 * 2
def baseEnd_1766270 : Nat := 906945475616909694202079

theorem tailTrace_1766270 : CollatzResearch.WordTrace tailWord_1766270 prefixEnd_1766270 906945475616909694202079 := by
  unfold tailWord_1766270
  simp only [CollatzResearch.WordTrace]
  refine ⟨8052644913889114968142033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42947439540741946496757509 8052644913889114968142033)
  ·
    refine ⟨6039483685416836226106525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8052644913889114968142033 6039483685416836226106525)
    ·
      refine ⟨2264806382031313584789947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6039483685416836226106525 2264806382031313584789947)
      ·
        refine ⟨3397209573046970377184921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2264806382031313584789947 3397209573046970377184921)
        ·
          refine ⟨2547907179785227782888691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3397209573046970377184921 2547907179785227782888691)
          ·
            refine ⟨3821860769677841674333037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2547907179785227782888691 3821860769677841674333037)
            ·
              refine ⟨1433197788629190627874889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3821860769677841674333037 1433197788629190627874889)
              ·
                refine ⟨1074898341471892970906167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1433197788629190627874889 1074898341471892970906167)
                ·
                  refine ⟨1612347512207839456359251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1074898341471892970906167 1612347512207839456359251)
                  ·
                    refine ⟨2418521268311759184538877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1612347512207839456359251 2418521268311759184538877)
                    ·
                      refine ⟨906945475616909694202079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2418521268311759184538877 906945475616909694202079)
                      ·
                        rfl

theorem cell23_1766270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_1766270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766270 prefixEnd_1766270 := by exact prefixLift 1766270
  have htrace : WordTrace (prefixWord ++ tailWord_1766270) baseStart_1766270 baseEnd_1766270 := by
    simpa [prefixWord, tailWord_1766270, baseEnd_1766270] using wordTrace_append hprefix tailTrace_1766270
  have hstable : (prefixWord ++ tailWord_1766270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766270).length < 2 ^ (prefixWord ++ tailWord_1766270).sum := by decide
  have hdescent : baseEnd_1766270 < baseStart_1766270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766292 : List Nat := [2, 4, 2, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_1766292 : Nat := 118140960795 + 1766292 * 2 ^ 59
def prefixEnd_1766292 : Nat := 4983230072969 + 3 ^ 40 * 1766292 * 2
def baseEnd_1766292 : Nat := 906956772191308608126977

theorem tailTrace_1766292 : CollatzResearch.WordTrace tailWord_1766292 prefixEnd_1766292 906956772191308608126977 := by
  unfold tailWord_1766292
  simp only [CollatzResearch.WordTrace]
  refine ⟨32210980858516608751218565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42947974478022145001624753 32210980858516608751218565)
  ·
    refine ⟨6039558910971864140853481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32210980858516608751218565 6039558910971864140853481)
    ·
      refine ⟨4529669183228898105640111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6039558910971864140853481 4529669183228898105640111)
      ·
        refine ⟨6794503774843347158460167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4529669183228898105640111 6794503774843347158460167)
        ·
          refine ⟨10191755662265020737690251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6794503774843347158460167 10191755662265020737690251)
          ·
            refine ⟨15287633493397531106535377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10191755662265020737690251 15287633493397531106535377)
            ·
              refine ⟨11465725120048148329901533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15287633493397531106535377 11465725120048148329901533)
              ·
                refine ⟨4299646920018055623713075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11465725120048148329901533 4299646920018055623713075)
                ·
                  refine ⟨6449470380027083435569613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4299646920018055623713075 6449470380027083435569613)
                  ·
                    refine ⟨2418551392510156288338605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6449470380027083435569613 2418551392510156288338605)
                    ·
                      refine ⟨906956772191308608126977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2418551392510156288338605 906956772191308608126977)
                      ·
                        rfl

theorem cell23_1766292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_1766292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766292 prefixEnd_1766292 := by exact prefixLift 1766292
  have htrace : WordTrace (prefixWord ++ tailWord_1766292) baseStart_1766292 baseEnd_1766292 := by
    simpa [prefixWord, tailWord_1766292, baseEnd_1766292] using wordTrace_append hprefix tailTrace_1766292
  have hstable : (prefixWord ++ tailWord_1766292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766292).length < 2 ^ (prefixWord ++ tailWord_1766292).sum := by decide
  have hdescent : baseEnd_1766292 < baseStart_1766292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766325 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 2, 6]
def baseStart_1766325 : Nat := 118140960795 + 1766325 * 2 ^ 59
def prefixEnd_1766325 : Nat := 4983230072969 + 3 ^ 40 * 1766325 * 2
def baseEnd_1766325 : Nat := 302324572350968993004775

theorem tailTrace_1766325 : CollatzResearch.WordTrace tailWord_1766325 prefixEnd_1766325 302324572350968993004775 := by
  unfold tailWord_1766325
  simp only [CollatzResearch.WordTrace]
  refine ⟨64423165325913664138388429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42948776883942442758925619 64423165325913664138388429)
  ·
    refine ⟨24158686997217624051895661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64423165325913664138388429 24158686997217624051895661)
    ·
      refine ⟨9059507623956609019460873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24158686997217624051895661 9059507623956609019460873)
      ·
        refine ⟨6794630717967456764595655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9059507623956609019460873 6794630717967456764595655)
        ·
          refine ⟨10191946076951185146893483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6794630717967456764595655 10191946076951185146893483)
          ·
            refine ⟨15287919115426777720340225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10191946076951185146893483 15287919115426777720340225)
            ·
              refine ⟨11465939336570083290255169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15287919115426777720340225 11465939336570083290255169)
              ·
                refine ⟨8599454502427562467691377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11465939336570083290255169 8599454502427562467691377)
                ·
                  refine ⟨6449590876820671850768533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8599454502427562467691377 6449590876820671850768533)
                  ·
                    refine ⟨302324572350968993004775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6449590876820671850768533 302324572350968993004775)
                    ·
                      rfl

theorem cell23_1766325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_1766325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766325 prefixEnd_1766325 := by exact prefixLift 1766325
  have htrace : WordTrace (prefixWord ++ tailWord_1766325) baseStart_1766325 baseEnd_1766325 := by
    simpa [prefixWord, tailWord_1766325, baseEnd_1766325] using wordTrace_append hprefix tailTrace_1766325
  have hstable : (prefixWord ++ tailWord_1766325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766325).length < 2 ^ (prefixWord ++ tailWord_1766325).sum := by decide
  have hdescent : baseEnd_1766325 < baseStart_1766325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766370 : List Nat := [3, 3, 3, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_1766370 : Nat := 118140960795 + 1766370 * 2 ^ 59
def prefixEnd_1766370 : Nat := 4983230072969 + 3 ^ 40 * 1766370 * 2
def baseEnd_1766370 : Nat := 906996823682359302951619

theorem tailTrace_1766370 : CollatzResearch.WordTrace tailWord_1766370 prefixEnd_1766370 906996823682359302951619 := by
  unfold tailWord_1766370
  simp only [CollatzResearch.WordTrace]
  refine ⟨16106201652687659205944141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42949871073833757882517709 16106201652687659205944141)
  ·
    refine ⟨6039825619757872202229053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16106201652687659205944141 6039825619757872202229053)
    ·
      refine ⟨2264934607409202075835895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6039825619757872202229053 2264934607409202075835895)
      ·
        refine ⟨3397401911113803113753843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2264934607409202075835895 3397401911113803113753843)
        ·
          refine ⟨5096102866670704670630765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3397401911113803113753843 5096102866670704670630765)
          ·
            refine ⟨1911038575001514251486537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5096102866670704670630765 1911038575001514251486537)
            ·
              refine ⟨1433278931251135688614903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1911038575001514251486537 1433278931251135688614903)
              ·
                refine ⟨2149918396876703532922355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1433278931251135688614903 2149918396876703532922355)
                ·
                  refine ⟨3224877595315055299383533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2149918396876703532922355 3224877595315055299383533)
                  ·
                    refine ⟨1209329098243145737268825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3224877595315055299383533 1209329098243145737268825)
                    ·
                      refine ⟨906996823682359302951619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1209329098243145737268825 906996823682359302951619)
                      ·
                        rfl

theorem cell23_1766370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_1766370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766370 prefixEnd_1766370 := by exact prefixLift 1766370
  have htrace : WordTrace (prefixWord ++ tailWord_1766370) baseStart_1766370 baseEnd_1766370 := by
    simpa [prefixWord, tailWord_1766370, baseEnd_1766370] using wordTrace_append hprefix tailTrace_1766370
  have hstable : (prefixWord ++ tailWord_1766370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766370).length < 2 ^ (prefixWord ++ tailWord_1766370).sum := by decide
  have hdescent : baseEnd_1766370 < baseStart_1766370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766405 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 3, 3, 4]
def baseStart_1766405 : Nat := 118140960795 + 1766405 * 2 ^ 59
def prefixEnd_1766405 : Nat := 4983230072969 + 3 ^ 40 * 1766405 * 2
def baseEnd_1766405 : Nat := 907014795505266666013957

theorem tailTrace_1766405 : CollatzResearch.WordTrace tailWord_1766405 prefixEnd_1766405 907014795505266666013957 := by
  unfold tailWord_1766405
  simp only [CollatzResearch.WordTrace]
  refine ⟨64426083165623837801300669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42950722110415891867533779 64426083165623837801300669)
  ·
    refine ⟨24159781187108939175487751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64426083165623837801300669 24159781187108939175487751)
    ·
      refine ⟨36239671780663408763231627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24159781187108939175487751 36239671780663408763231627)
      ·
        refine ⟨54359507670995113144847441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36239671780663408763231627 54359507670995113144847441)
        ·
          refine ⟨40769630753246334858635581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54359507670995113144847441 40769630753246334858635581)
          ·
            refine ⟨15288611532467375571988343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40769630753246334858635581 15288611532467375571988343)
            ·
              refine ⟨22932917298701063357982515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15288611532467375571988343 22932917298701063357982515)
              ·
                refine ⟨34399375948051595036973773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22932917298701063357982515 34399375948051595036973773)
                ·
                  refine ⟨12899765980519348138865165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34399375948051595036973773 12899765980519348138865165)
                  ·
                    refine ⟨4837412242694755552074437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12899765980519348138865165 4837412242694755552074437)
                    ·
                      refine ⟨907014795505266666013957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4837412242694755552074437 907014795505266666013957)
                      ·
                        rfl

theorem cell23_1766405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_1766405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766405 prefixEnd_1766405 := by exact prefixLift 1766405
  have htrace : WordTrace (prefixWord ++ tailWord_1766405) baseStart_1766405 baseEnd_1766405 := by
    simpa [prefixWord, tailWord_1766405, baseEnd_1766405] using wordTrace_append hprefix tailTrace_1766405
  have hstable : (prefixWord ++ tailWord_1766405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766405).length < 2 ^ (prefixWord ++ tailWord_1766405).sum := by decide
  have hdescent : baseEnd_1766405 < baseStart_1766405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766439 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1766439 : Nat := 118140960795 + 1766439 * 2 ^ 59
def prefixEnd_1766439 : Nat := 4983230072969 + 3 ^ 40 * 1766439 * 2
def baseEnd_1766439 : Nat := 907032253847519532988801

theorem tailTrace_1766439 : CollatzResearch.WordTrace tailWord_1766439 prefixEnd_1766439 907032253847519532988801 := by
  unfold tailWord_1766439
  simp only [CollatzResearch.WordTrace]
  refine ⟨64427323247500661608038371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42951548831667107738692247 64427323247500661608038371)
  ·
    refine ⟨96640984871250992412057557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64427323247500661608038371 96640984871250992412057557)
    ·
      refine ⟨2265023082919945134657599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 96640984871250992412057557 2265023082919945134657599)
      ·
        refine ⟨3397534624379917701986399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2265023082919945134657599 3397534624379917701986399)
        ·
          refine ⟨5096301936569876552979599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3397534624379917701986399 5096301936569876552979599)
          ·
            refine ⟨7644452904854814829469399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5096301936569876552979599 7644452904854814829469399)
            ·
              refine ⟨11466679357282222244204099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7644452904854814829469399 11466679357282222244204099)
              ·
                refine ⟨17200019035923333366306149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11466679357282222244204099 17200019035923333366306149)
                ·
                  refine ⟨3225003569235625006182403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17200019035923333366306149 3225003569235625006182403)
                  ·
                    refine ⟨4837505353853437509273605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3225003569235625006182403 4837505353853437509273605)
                    ·
                      refine ⟨907032253847519532988801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4837505353853437509273605 907032253847519532988801)
                      ·
                        rfl

theorem cell23_1766439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1766439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766439 prefixEnd_1766439 := by exact prefixLift 1766439
  have htrace : WordTrace (prefixWord ++ tailWord_1766439) baseStart_1766439 baseEnd_1766439 := by
    simpa [prefixWord, tailWord_1766439, baseEnd_1766439] using wordTrace_append hprefix tailTrace_1766439
  have hstable : (prefixWord ++ tailWord_1766439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766439).length < 2 ^ (prefixWord ++ tailWord_1766439).sum := by decide
  have hdescent : baseEnd_1766439 < baseStart_1766439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766512 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 4]
def baseStart_1766512 : Nat := 118140960795 + 1766512 * 2 ^ 59
def prefixEnd_1766512 : Nat := 4983230072969 + 3 ^ 40 * 1766512 * 2
def baseEnd_1766512 : Nat := 907069737935297747375965

theorem tailTrace_1766512 : CollatzResearch.WordTrace tailWord_1766512 prefixEnd_1766512 907069737935297747375965 := by
  unfold tailWord_1766512
  simp only [CollatzResearch.WordTrace]
  refine ⟨32214992888118097537722895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42953323850824130050297193 32214992888118097537722895)
  ·
    refine ⟨48322489332177146306584343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32214992888118097537722895 48322489332177146306584343)
    ·
      refine ⟨72483733998265719459876515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48322489332177146306584343 72483733998265719459876515)
      ·
        refine ⟨108725600997398579189814773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72483733998265719459876515 108725600997398579189814773)
        ·
          refine ⟨10193025093506116799045135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108725600997398579189814773 10193025093506116799045135)
          ·
            refine ⟨15289537640259175198567703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10193025093506116799045135 15289537640259175198567703)
            ·
              refine ⟨22934306460388762797851555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15289537640259175198567703 22934306460388762797851555)
              ·
                refine ⟨34401459690583144196777333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22934306460388762797851555 34401459690583144196777333)
                ·
                  refine ⟨3225136845992169768447875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34401459690583144196777333 3225136845992169768447875)
                  ·
                    refine ⟨4837705268988254652671813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3225136845992169768447875 4837705268988254652671813)
                    ·
                      refine ⟨907069737935297747375965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4837705268988254652671813 907069737935297747375965)
                      ·
                        rfl

theorem cell23_1766512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 4].length) (baseStart_1766512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766512 prefixEnd_1766512 := by exact prefixLift 1766512
  have htrace : WordTrace (prefixWord ++ tailWord_1766512) baseStart_1766512 baseEnd_1766512 := by
    simpa [prefixWord, tailWord_1766512, baseEnd_1766512] using wordTrace_append hprefix tailTrace_1766512
  have hstable : (prefixWord ++ tailWord_1766512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766512).length < 2 ^ (prefixWord ++ tailWord_1766512).sum := by decide
  have hdescent : baseEnd_1766512 < baseStart_1766512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766529 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_1766529 : Nat := 118140960795 + 1766529 * 2 ^ 59
def prefixEnd_1766529 : Nat := 4983230072969 + 3 ^ 40 * 1766529 * 2
def baseEnd_1766529 : Nat := 907078467106424180863387

theorem tailTrace_1766529 : CollatzResearch.WordTrace tailWord_1766529 prefixEnd_1766529 907078467106424180863387 := by
  unfold tailWord_1766529
  simp only [CollatzResearch.WordTrace]
  refine ⟨64430605817174606978814641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42953737211449737985876427 64430605817174606978814641)
  ·
    refine ⟨48322954362880955234110981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64430605817174606978814641 48322954362880955234110981)
    ·
      refine ⟨9060553943040179106395809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48322954362880955234110981 9060553943040179106395809)
      ·
        refine ⟨6795415457280134329796857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9060553943040179106395809 6795415457280134329796857)
        ·
          refine ⟨5096561592960100747347643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6795415457280134329796857 5096561592960100747347643)
          ·
            refine ⟨7644842389440151121021465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5096561592960100747347643 7644842389440151121021465)
            ·
              refine ⟨5733631792080113340766099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7644842389440151121021465 5733631792080113340766099)
              ·
                refine ⟨8600447688120170011149149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5733631792080113340766099 8600447688120170011149149)
                ·
                  refine ⟨3225167883045063754180931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8600447688120170011149149 3225167883045063754180931)
                  ·
                    refine ⟨4837751824567595631271397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3225167883045063754180931 4837751824567595631271397)
                    ·
                      refine ⟨907078467106424180863387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4837751824567595631271397 907078467106424180863387)
                      ·
                        rfl

theorem cell23_1766529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_1766529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766529 prefixEnd_1766529 := by exact prefixLift 1766529
  have htrace : WordTrace (prefixWord ++ tailWord_1766529) baseStart_1766529 baseEnd_1766529 := by
    simpa [prefixWord, tailWord_1766529, baseEnd_1766529] using wordTrace_append hprefix tailTrace_1766529
  have hstable : (prefixWord ++ tailWord_1766529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766529).length < 2 ^ (prefixWord ++ tailWord_1766529).sum := by decide
  have hdescent : baseEnd_1766529 < baseStart_1766529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766533 : List Nat := [1, 3, 1, 1, 6, 2, 1, 1, 2, 3, 2]
def baseStart_1766533 : Nat := 118140960795 + 1766533 * 2 ^ 59
def prefixEnd_1766533 : Nat := 4983230072969 + 3 ^ 40 * 1766533 * 2
def baseEnd_1766533 : Nat := 907080521029042165213369

theorem tailTrace_1766533 : CollatzResearch.WordTrace tailWord_1766533 prefixEnd_1766533 907080521029042165213369 := by
  unfold tailWord_1766533
  simp only [CollatzResearch.WordTrace]
  refine ⟨64430751709160115661960253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42953834472773410441306835 64430751709160115661960253)
  ·
    refine ⟨24161531890935043373235095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64430751709160115661960253 24161531890935043373235095)
    ·
      refine ⟨36242297836402565059852643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24161531890935043373235095 36242297836402565059852643)
      ·
        refine ⟨54363446754603847589778965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36242297836402565059852643 54363446754603847589778965)
        ·
          refine ⟨2548286566622055355770889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54363446754603847589778965 2548286566622055355770889)
          ·
            refine ⟨1911214924966541516828167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2548286566622055355770889 1911214924966541516828167)
            ·
              refine ⟨2866822387449812275242251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1911214924966541516828167 2866822387449812275242251)
              ·
                refine ⟨4300233581174718412863377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2866822387449812275242251 4300233581174718412863377)
                ·
                  refine ⟨3225175185881038809647533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4300233581174718412863377 3225175185881038809647533)
                  ·
                    refine ⟨1209440694705389553617825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3225175185881038809647533 1209440694705389553617825)
                    ·
                      refine ⟨907080521029042165213369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1209440694705389553617825 907080521029042165213369)
                      ·
                        rfl

theorem cell23_1766533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 3, 2].length) (baseStart_1766533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766533 prefixEnd_1766533 := by exact prefixLift 1766533
  have htrace : WordTrace (prefixWord ++ tailWord_1766533) baseStart_1766533 baseEnd_1766533 := by
    simpa [prefixWord, tailWord_1766533, baseEnd_1766533] using wordTrace_append hprefix tailTrace_1766533
  have hstable : (prefixWord ++ tailWord_1766533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766533).length < 2 ^ (prefixWord ++ tailWord_1766533).sum := by decide
  have hdescent : baseEnd_1766533 < baseStart_1766533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766546 : List Nat := [3, 2, 3, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_1766546 : Nat := 118140960795 + 1766546 * 2 ^ 59
def prefixEnd_1766546 : Nat := 4983230072969 + 3 ^ 40 * 1766546 * 2
def baseEnd_1766546 : Nat := 907087196277550614350809

theorem tailTrace_1766546 : CollatzResearch.WordTrace tailWord_1766546 prefixEnd_1766546 907087196277550614350809 := by
  unfold tailWord_1766546
  simp only [CollatzResearch.WordTrace]
  refine ⟨16107806464528254720545873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42954150572075345921455661 16107806464528254720545873)
  ·
    refine ⟨12080854848396191040409405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16107806464528254720545873 12080854848396191040409405)
    ·
      refine ⟨4530320568148571640153527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12080854848396191040409405 4530320568148571640153527)
      ·
        refine ⟨6795480852222857460230291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4530320568148571640153527 6795480852222857460230291)
        ·
          refine ⟨10193221278334286190345437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6795480852222857460230291 10193221278334286190345437)
          ·
            refine ⟨3822457979375357321379539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10193221278334286190345437 3822457979375357321379539)
            ·
              refine ⟨5733686969063035982069309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3822457979375357321379539 5733686969063035982069309)
              ·
                refine ⟨2150132613398638493275991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5733686969063035982069309 2150132613398638493275991)
                ·
                  refine ⟨3225198920097957739913987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2150132613398638493275991 3225198920097957739913987)
                  ·
                    refine ⟨4837798380146936609870981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3225198920097957739913987 4837798380146936609870981)
                    ·
                      refine ⟨907087196277550614350809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4837798380146936609870981 907087196277550614350809)
                      ·
                        rfl

theorem cell23_1766546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_1766546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766546 prefixEnd_1766546 := by exact prefixLift 1766546
  have htrace : WordTrace (prefixWord ++ tailWord_1766546) baseStart_1766546 baseEnd_1766546 := by
    simpa [prefixWord, tailWord_1766546, baseEnd_1766546] using wordTrace_append hprefix tailTrace_1766546
  have hstable : (prefixWord ++ tailWord_1766546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766546).length < 2 ^ (prefixWord ++ tailWord_1766546).sum := by decide
  have hdescent : baseEnd_1766546 < baseStart_1766546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766552 : List Nat := [2, 1, 2, 4, 2, 2, 10]
def baseStart_1766552 : Nat := 118140960795 + 1766552 * 2 ^ 59
def prefixEnd_1766552 : Nat := 4983230072969 + 3 ^ 40 * 1766552 * 2
def baseEnd_1766552 : Nat := 11198645397055278899701

theorem tailTrace_1766552 : CollatzResearch.WordTrace tailWord_1766552 prefixEnd_1766552 11198645397055278899701 := by
  unfold tailWord_1766552
  simp only [CollatzResearch.WordTrace]
  refine ⟨32215722348045640953450955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42954296464060854604601273 32215722348045640953450955)
  ·
    refine ⟨48323583522068461430176433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32215722348045640953450955 48323583522068461430176433)
    ·
      refine ⟨36242687641551346072632325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48323583522068461430176433 36242687641551346072632325)
      ·
        refine ⟨6795503932790877388618561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36242687641551346072632325 6795503932790877388618561)
        ·
          refine ⟨5096627949593158041463921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6795503932790877388618561 5096627949593158041463921)
          ·
            refine ⟨3822470962194868531097941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5096627949593158041463921 3822470962194868531097941)
            ·
              refine ⟨11198645397055278899701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3822470962194868531097941 11198645397055278899701)
              ·
                rfl

theorem cell23_1766552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 10].length) (baseStart_1766552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766552 prefixEnd_1766552 := by exact prefixLift 1766552
  have htrace : WordTrace (prefixWord ++ tailWord_1766552) baseStart_1766552 baseEnd_1766552 := by
    simpa [prefixWord, tailWord_1766552, baseEnd_1766552] using wordTrace_append hprefix tailTrace_1766552
  have hstable : (prefixWord ++ tailWord_1766552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766552).length < 2 ^ (prefixWord ++ tailWord_1766552).sum := by decide
  have hdescent : baseEnd_1766552 < baseStart_1766552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766556 : List Nat := [2, 2, 3, 2, 1, 2, 3, 2, 2, 4]
def baseStart_1766556 : Nat := 118140960795 + 1766556 * 2 ^ 59
def prefixEnd_1766556 : Nat := 4983230072969 + 3 ^ 40 * 1766556 * 2
def baseEnd_1766556 : Nat := 302364110361365191741921

theorem tailTrace_1766556 : CollatzResearch.WordTrace tailWord_1766556 prefixEnd_1766556 302364110361365191741921 := by
  unfold tailWord_1766556
  simp only [CollatzResearch.WordTrace]
  refine ⟨32215795294038395295023761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42954393725384527060031681 32215795294038395295023761)
  ·
    refine ⟨24161846470528796471267821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32215795294038395295023761 24161846470528796471267821)
    ·
      refine ⟨9060692426448298676725433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24161846470528796471267821 9060692426448298676725433)
      ·
        refine ⟨6795519319836224007544075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9060692426448298676725433 6795519319836224007544075)
        ·
          refine ⟨10193278979754336011316113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6795519319836224007544075 10193278979754336011316113)
          ·
            refine ⟨7644959234815752008487085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10193278979754336011316113 7644959234815752008487085)
            ·
              refine ⟨2866859713055907003182657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7644959234815752008487085 2866859713055907003182657)
              ·
                refine ⟨2150144784791930252386993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2866859713055907003182657 2150144784791930252386993)
                ·
                  refine ⟨1612608588593947689290245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2150144784791930252386993 1612608588593947689290245)
                  ·
                    refine ⟨302364110361365191741921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1612608588593947689290245 302364110361365191741921)
                    ·
                      rfl

theorem cell23_1766556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_1766556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766556 prefixEnd_1766556 := by exact prefixLift 1766556
  have htrace : WordTrace (prefixWord ++ tailWord_1766556) baseStart_1766556 baseEnd_1766556 := by
    simpa [prefixWord, tailWord_1766556, baseEnd_1766556] using wordTrace_append hprefix tailTrace_1766556
  have hstable : (prefixWord ++ tailWord_1766556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766556).length < 2 ^ (prefixWord ++ tailWord_1766556).sum := by decide
  have hdescent : baseEnd_1766556 < baseStart_1766556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766573 : List Nat := [1, 5, 2, 1, 4, 1, 1, 1, 1, 6]
def baseStart_1766573 : Nat := 118140960795 + 1766573 * 2 ^ 59
def prefixEnd_1766573 : Nat := 4983230072969 + 3 ^ 40 * 1766573 * 2
def baseEnd_1766573 : Nat := 302367020085074002904395

theorem tailTrace_1766573 : CollatzResearch.WordTrace tailWord_1766573 prefixEnd_1766573 302367020085074002904395 := by
  unfold tailWord_1766573
  simp only [CollatzResearch.WordTrace]
  refine ⟨64432210629015202493416373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42954807086010134995610915 64432210629015202493416373)
  ·
    refine ⟨6040519746470175233757785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64432210629015202493416373 6040519746470175233757785)
    ·
      refine ⟨4530389809852631425318339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6040519746470175233757785 4530389809852631425318339)
      ·
        refine ⟨6795584714778947137977509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4530389809852631425318339 6795584714778947137977509)
        ·
          refine ⟨1274172134021052588370783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6795584714778947137977509 1274172134021052588370783)
          ·
            refine ⟨1911258201031578882556175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274172134021052588370783 1911258201031578882556175)
            ·
              refine ⟨2866887301547368323834263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1911258201031578882556175 2866887301547368323834263)
              ·
                refine ⟨4300330952321052485751395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2866887301547368323834263 4300330952321052485751395)
                ·
                  refine ⟨6450496428481578728627093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4300330952321052485751395 6450496428481578728627093)
                  ·
                    refine ⟨302367020085074002904395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6450496428481578728627093 302367020085074002904395)
                    ·
                      rfl

theorem cell23_1766573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_1766573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766573 prefixEnd_1766573 := by exact prefixLift 1766573
  have htrace : WordTrace (prefixWord ++ tailWord_1766573) baseStart_1766573 baseEnd_1766573 := by
    simpa [prefixWord, tailWord_1766573, baseEnd_1766573] using wordTrace_append hprefix tailTrace_1766573
  have hstable : (prefixWord ++ tailWord_1766573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766573).length < 2 ^ (prefixWord ++ tailWord_1766573).sum := by decide
  have hdescent : baseEnd_1766573 < baseStart_1766573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766579 : List Nat := [1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 3]
def baseStart_1766579 : Nat := 118140960795 + 1766579 * 2 ^ 59
def prefixEnd_1766579 : Nat := 4983230072969 + 3 ^ 40 * 1766579 * 2
def baseEnd_1766579 : Nat := 907104141139148985238157

theorem tailTrace_1766579 : CollatzResearch.WordTrace tailWord_1766579 prefixEnd_1766579 907104141139148985238157 := by
  unfold tailWord_1766579
  simp only [CollatzResearch.WordTrace]
  refine ⟨64432429466993465518134791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42954952977995643678756527 64432429466993465518134791)
  ·
    refine ⟨96648644200490198277202187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64432429466993465518134791 96648644200490198277202187)
    ·
      refine ⟨144972966300735297415803281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96648644200490198277202187 144972966300735297415803281)
      ·
        refine ⟨108729724725551473061852461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144972966300735297415803281 108729724725551473061852461)
        ·
          refine ⟨40773646772081802398194673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108729724725551473061852461 40773646772081802398194673)
          ·
            refine ⟨30580235079061351798646005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40773646772081802398194673 30580235079061351798646005)
            ·
              refine ⟨2866897038662001731123063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30580235079061351798646005 2866897038662001731123063)
              ·
                refine ⟨4300345557993002596684595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2866897038662001731123063 4300345557993002596684595)
                ·
                  refine ⟨6450518336989503895026893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4300345557993002596684595 6450518336989503895026893)
                  ·
                    refine ⟨2418944376371063960635085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6450518336989503895026893 2418944376371063960635085)
                    ·
                      refine ⟨907104141139148985238157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2418944376371063960635085 907104141139148985238157)
                      ·
                        rfl

theorem cell23_1766579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 3].length) (baseStart_1766579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766579 prefixEnd_1766579 := by exact prefixLift 1766579
  have htrace : WordTrace (prefixWord ++ tailWord_1766579) baseStart_1766579 baseEnd_1766579 := by
    simpa [prefixWord, tailWord_1766579, baseEnd_1766579] using wordTrace_append hprefix tailTrace_1766579
  have hstable : (prefixWord ++ tailWord_1766579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766579).length < 2 ^ (prefixWord ++ tailWord_1766579).sum := by decide
  have hdescent : baseEnd_1766579 < baseStart_1766579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766614 : List Nat := [5, 2, 1, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_1766614 : Nat := 118140960795 + 1766614 * 2 ^ 59
def prefixEnd_1766614 : Nat := 4983230072969 + 3 ^ 40 * 1766614 * 2
def baseEnd_1766614 : Nat := 907122112962056348300497

theorem tailTrace_1766614 : CollatzResearch.WordTrace tailWord_1766614 prefixEnd_1766614 907122112962056348300497 := by
  unfold tailWord_1766614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4027106626366666655978681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42955804014577777663772597 4027106626366666655978681)
  ·
    refine ⟨3020329969774999991984011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4027106626366666655978681 3020329969774999991984011)
    ·
      refine ⟨4530494954662499987976017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3020329969774999991984011 4530494954662499987976017)
      ·
        refine ⟨3397871215996874990982013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4530494954662499987976017 3397871215996874990982013)
        ·
          refine ⟨1274201705998828121618255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3397871215996874990982013 1274201705998828121618255)
          ·
            refine ⟨1911302558998242182427383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274201705998828121618255 1911302558998242182427383)
            ·
              refine ⟨2866953838497363273641075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1911302558998242182427383 2866953838497363273641075)
              ·
                refine ⟨4300430757746044910461613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2866953838497363273641075 4300430757746044910461613)
                ·
                  refine ⟨1612661534154766841423105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4300430757746044910461613 1612661534154766841423105)
                  ·
                    refine ⟨1209496150616075131067329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1612661534154766841423105 1209496150616075131067329)
                    ·
                      refine ⟨907122112962056348300497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1209496150616075131067329 907122112962056348300497)
                      ·
                        rfl

theorem cell23_1766614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_1766614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766614 prefixEnd_1766614 := by exact prefixLift 1766614
  have htrace : WordTrace (prefixWord ++ tailWord_1766614) baseStart_1766614 baseEnd_1766614 := by
    simpa [prefixWord, tailWord_1766614, baseEnd_1766614] using wordTrace_append hprefix tailTrace_1766614
  have hstable : (prefixWord ++ tailWord_1766614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766614).length < 2 ^ (prefixWord ++ tailWord_1766614).sum := by decide
  have hdescent : baseEnd_1766614 < baseStart_1766614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766670 : List Nat := [4, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2]
def baseStart_1766670 : Nat := 118140960795 + 1766670 * 2 ^ 59
def prefixEnd_1766670 : Nat := 4983230072969 + 3 ^ 40 * 1766670 * 2
def baseEnd_1766670 : Nat := 907150867878708129200239

theorem tailTrace_1766670 : CollatzResearch.WordTrace tailWord_1766670 prefixEnd_1766670 907150867878708129200239 := by
  unfold tailWord_1766670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8054468563707973507462183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42957165673109192039798309 8054468563707973507462183)
  ·
    refine ⟨12081702845561960261193275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8054468563707973507462183 12081702845561960261193275)
    ·
      refine ⟨18122554268342940391789913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12081702845561960261193275 18122554268342940391789913)
      ·
        refine ⟨13591915701257205293842435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18122554268342940391789913 13591915701257205293842435)
        ·
          refine ⟨20387873551885807940763653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13591915701257205293842435 20387873551885807940763653)
          ·
            refine ⟨3822726290978588988893185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20387873551885807940763653 3822726290978588988893185)
            ·
              refine ⟨2867044718233941741669889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3822726290978588988893185 2867044718233941741669889)
              ·
                refine ⟨2150283538675456306252417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2867044718233941741669889 2150283538675456306252417)
                ·
                  refine ⟨1612712654006592229689313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2150283538675456306252417 1612712654006592229689313)
                  ·
                    refine ⟨1209534490504944172266985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1612712654006592229689313 1209534490504944172266985)
                    ·
                      refine ⟨907150867878708129200239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1209534490504944172266985 907150867878708129200239)
                      ·
                        rfl

theorem cell23_1766670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_1766670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766670 prefixEnd_1766670 := by exact prefixLift 1766670
  have htrace : WordTrace (prefixWord ++ tailWord_1766670) baseStart_1766670 baseEnd_1766670 := by
    simpa [prefixWord, tailWord_1766670, baseEnd_1766670] using wordTrace_append hprefix tailTrace_1766670
  have hstable : (prefixWord ++ tailWord_1766670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766670).length < 2 ^ (prefixWord ++ tailWord_1766670).sum := by decide
  have hdescent : baseEnd_1766670 < baseStart_1766670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766706 : List Nat := [3, 2, 1, 1, 4, 1, 3, 1, 2, 5]
def baseStart_1766706 : Nat := 118140960795 + 1766706 * 2 ^ 59
def prefixEnd_1766706 : Nat := 4983230072969 + 3 ^ 40 * 1766706 * 2
def baseEnd_1766706 : Nat := 302389784394089996116691

theorem tailTrace_1766706 : CollatzResearch.WordTrace tailWord_1766706 prefixEnd_1766706 302389784394089996116691 := by
  unfold tailWord_1766706
  simp only [CollatzResearch.WordTrace]
  refine ⟨16109265384383341552001993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42958041025022244138671981 16109265384383341552001993)
  ·
    refine ⟨12081949038287506164001495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16109265384383341552001993 12081949038287506164001495)
    ·
      refine ⟨18122923557431259246002243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12081949038287506164001495 18122923557431259246002243)
      ·
        refine ⟨27184385336146888869003365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18122923557431259246002243 27184385336146888869003365)
        ·
          refine ⟨5097072250527541662938131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27184385336146888869003365 5097072250527541662938131)
          ·
            refine ⟨7645608375791312494407197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5097072250527541662938131 7645608375791312494407197)
            ·
              refine ⟨2867103140921742185402699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7645608375791312494407197 2867103140921742185402699)
              ·
                refine ⟨4300654711382613278104049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2867103140921742185402699 4300654711382613278104049)
                ·
                  refine ⟨3225491033536959958578037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4300654711382613278104049 3225491033536959958578037)
                  ·
                    refine ⟨302389784394089996116691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3225491033536959958578037 302389784394089996116691)
                    ·
                      rfl

theorem cell23_1766706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_1766706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766706 prefixEnd_1766706 := by exact prefixLift 1766706
  have htrace : WordTrace (prefixWord ++ tailWord_1766706) baseStart_1766706 baseEnd_1766706 := by
    simpa [prefixWord, tailWord_1766706, baseEnd_1766706] using wordTrace_append hprefix tailTrace_1766706
  have hstable : (prefixWord ++ tailWord_1766706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766706).length < 2 ^ (prefixWord ++ tailWord_1766706).sum := by decide
  have hdescent : baseEnd_1766706 < baseStart_1766706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766736 : List Nat := [2, 1, 1, 1, 1, 5, 4, 1, 3, 4]
def baseStart_1766736 : Nat := 118140960795 + 1766736 * 2 ^ 59
def prefixEnd_1766736 : Nat := 4983230072969 + 3 ^ 40 * 1766736 * 2
def baseEnd_1766736 : Nat := 302394919200634956991645

theorem tailTrace_1766736 : CollatzResearch.WordTrace tailWord_1766736 prefixEnd_1766736 302394919200634956991645 := by
  unfold tailWord_1766736
  simp only [CollatzResearch.WordTrace]
  refine ⟨32219077863712340665800031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42958770484949787554400041 32219077863712340665800031)
  ·
    refine ⟨48328616795568510998700047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32219077863712340665800031 48328616795568510998700047)
    ·
      refine ⟨72492925193352766498050071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48328616795568510998700047 72492925193352766498050071)
      ·
        refine ⟨108739387790029149747075107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72492925193352766498050071 108739387790029149747075107)
        ·
          refine ⟨163109081685043724620612661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108739387790029149747075107 163109081685043724620612661)
          ·
            refine ⟨15291476407972849183182437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163109081685043724620612661 15291476407972849183182437)
            ·
              refine ⟨2867151826494909221846707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15291476407972849183182437 2867151826494909221846707)
              ·
                refine ⟨4300727739742363832770061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2867151826494909221846707 4300727739742363832770061)
                ·
                  refine ⟨1612772902403386437288773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4300727739742363832770061 1612772902403386437288773)
                  ·
                    refine ⟨302394919200634956991645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1612772902403386437288773 302394919200634956991645)
                    ·
                      rfl

theorem cell23_1766736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 3, 4].length) (baseStart_1766736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766736 prefixEnd_1766736 := by exact prefixLift 1766736
  have htrace : WordTrace (prefixWord ++ tailWord_1766736) baseStart_1766736 baseEnd_1766736 := by
    simpa [prefixWord, tailWord_1766736, baseEnd_1766736] using wordTrace_append hprefix tailTrace_1766736
  have hstable : (prefixWord ++ tailWord_1766736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766736).length < 2 ^ (prefixWord ++ tailWord_1766736).sum := by decide
  have hdescent : baseEnd_1766736 < baseStart_1766736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766813 : List Nat := [1, 4, 2, 1, 3, 1, 3, 2, 1, 5]
def baseStart_1766813 : Nat := 118140960795 + 1766813 * 2 ^ 59
def prefixEnd_1766813 : Nat := 4983230072969 + 3 ^ 40 * 1766813 * 2
def baseEnd_1766813 : Nat := 302408098537433689904027

theorem tailTrace_1766813 : CollatzResearch.WordTrace tailWord_1766813 prefixEnd_1766813 302408098537433689904027 := by
  unfold tailWord_1766813
  simp only [CollatzResearch.WordTrace]
  refine ⟨64440964148145723482153093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42960642765430482321435395 64440964148145723482153093)
  ·
    refine ⟨12082680777777323152903705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64440964148145723482153093 12082680777777323152903705)
    ·
      refine ⟨9062010583332992364677779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12082680777777323152903705 9062010583332992364677779)
      ·
        refine ⟨13593015874999488547016669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9062010583332992364677779 13593015874999488547016669)
        ·
          refine ⟨5097380953124808205131251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13593015874999488547016669 5097380953124808205131251)
          ·
            refine ⟨7646071429687212307696877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5097380953124808205131251 7646071429687212307696877)
            ·
              refine ⟨2867276786132704615386329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7646071429687212307696877 2867276786132704615386329)
              ·
                refine ⟨2150457589599528461539747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2867276786132704615386329 2150457589599528461539747)
                ·
                  refine ⟨3225686384399292692309621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2150457589599528461539747 3225686384399292692309621)
                  ·
                    refine ⟨302408098537433689904027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3225686384399292692309621 302408098537433689904027)
                    ·
                      rfl

theorem cell23_1766813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_1766813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766813 prefixEnd_1766813 := by exact prefixLift 1766813
  have htrace : WordTrace (prefixWord ++ tailWord_1766813) baseStart_1766813 baseEnd_1766813 := by
    simpa [prefixWord, tailWord_1766813, baseEnd_1766813] using wordTrace_append hprefix tailTrace_1766813
  have hstable : (prefixWord ++ tailWord_1766813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766813).length < 2 ^ (prefixWord ++ tailWord_1766813).sum := by decide
  have hdescent : baseEnd_1766813 < baseStart_1766813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766816 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 4]
def baseStart_1766816 : Nat := 118140960795 + 1766816 * 2 ^ 59
def prefixEnd_1766816 : Nat := 4983230072969 + 3 ^ 40 * 1766816 * 2
def baseEnd_1766816 : Nat := 907225836054264557974567

theorem tailTrace_1766816 : CollatzResearch.WordTrace tailWord_1766816 prefixEnd_1766816 907225836054264557974567 := by
  unfold tailWord_1766816
  simp only [CollatzResearch.WordTrace]
  refine ⟨32220536783567427497256151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42960715711423236663008201 32220536783567427497256151)
  ·
    refine ⟨48330805175351141245884227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32220536783567427497256151 48330805175351141245884227)
    ·
      refine ⟨72496207763026711868826341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48330805175351141245884227 72496207763026711868826341)
      ·
        refine ⟨13593038955567508475404939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72496207763026711868826341 13593038955567508475404939)
        ·
          refine ⟨20389558433351262713107409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13593038955567508475404939 20389558433351262713107409)
          ·
            refine ⟨15292168825013447034830557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20389558433351262713107409 15292168825013447034830557)
            ·
              refine ⟨5734563309380042638061459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15292168825013447034830557 5734563309380042638061459)
              ·
                refine ⟨8601844964070063957092189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5734563309380042638061459 8601844964070063957092189)
                ·
                  refine ⟨3225691861526273983909571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8601844964070063957092189 3225691861526273983909571)
                  ·
                    refine ⟨4838537792289410975864357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3225691861526273983909571 4838537792289410975864357)
                    ·
                      refine ⟨907225836054264557974567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4838537792289410975864357 907225836054264557974567)
                      ·
                        rfl

theorem cell23_1766816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_1766816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766816 prefixEnd_1766816 := by exact prefixLift 1766816
  have htrace : WordTrace (prefixWord ++ tailWord_1766816) baseStart_1766816 baseEnd_1766816 := by
    simpa [prefixWord, tailWord_1766816, baseEnd_1766816] using wordTrace_append hprefix tailTrace_1766816
  have hstable : (prefixWord ++ tailWord_1766816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766816).length < 2 ^ (prefixWord ++ tailWord_1766816).sum := by decide
  have hdescent : baseEnd_1766816 < baseStart_1766816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766846 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_1766846 : Nat := 118140960795 + 1766846 * 2 ^ 59
def prefixEnd_1766846 : Nat := 4983230072969 + 3 ^ 40 * 1766846 * 2
def baseEnd_1766846 : Nat := 907241240473899440599429

theorem tailTrace_1766846 : CollatzResearch.WordTrace tailWord_1766846 prefixEnd_1766846 907241240473899440599429 := by
  unfold tailWord_1766846
  simp only [CollatzResearch.WordTrace]
  refine ⟨8055270969628271264763049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42961445171350780078736261 8055270969628271264763049)
  ·
    refine ⟨6041453227221203448572287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8055270969628271264763049 6041453227221203448572287)
    ·
      refine ⟨9062179840831805172858431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6041453227221203448572287 9062179840831805172858431)
      ·
        refine ⟨13593269761247707759287647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9062179840831805172858431 13593269761247707759287647)
        ·
          refine ⟨20389904641871561638931471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13593269761247707759287647 20389904641871561638931471)
          ·
            refine ⟨30584856962807342458397207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20389904641871561638931471 30584856962807342458397207)
            ·
              refine ⟨45877285444211013687595811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30584856962807342458397207 45877285444211013687595811)
              ·
                refine ⟨68815928166316520531393717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45877285444211013687595811 68815928166316520531393717)
                ·
                  refine ⟨6451493265592173799818161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68815928166316520531393717 6451493265592173799818161)
                  ·
                    refine ⟨4838619949194130349863621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6451493265592173799818161 4838619949194130349863621)
                    ·
                      refine ⟨907241240473899440599429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4838619949194130349863621 907241240473899440599429)
                      ·
                        rfl

theorem cell23_1766846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_1766846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766846 prefixEnd_1766846 := by exact prefixLift 1766846
  have htrace : WordTrace (prefixWord ++ tailWord_1766846) baseStart_1766846 baseEnd_1766846 := by
    simpa [prefixWord, tailWord_1766846, baseEnd_1766846] using wordTrace_append hprefix tailTrace_1766846
  have hstable : (prefixWord ++ tailWord_1766846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766846).length < 2 ^ (prefixWord ++ tailWord_1766846).sum := by decide
  have hdescent : baseEnd_1766846 < baseStart_1766846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766859 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 6]
def baseStart_1766859 : Nat := 118140960795 + 1766859 * 2 ^ 59
def prefixEnd_1766859 : Nat := 4983230072969 + 3 ^ 40 * 1766859 * 2
def baseEnd_1766859 : Nat := 907247915722407889736869

theorem tailTrace_1766859 : CollatzResearch.WordTrace tailWord_1766859 prefixEnd_1766859 907247915722407889736869 := by
  unfold tailWord_1766859
  simp only [CollatzResearch.WordTrace]
  refine ⟨64442641905979073338327631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42961761270652715558885087 64442641905979073338327631)
  ·
    refine ⟨96663962858968610007491447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64442641905979073338327631 96663962858968610007491447)
    ·
      refine ⟨144995944288452915011237171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96663962858968610007491447 144995944288452915011237171)
      ·
        refine ⟨217493916432679372516855757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144995944288452915011237171 217493916432679372516855757)
        ·
          refine ⟨81560218662254764693820909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217493916432679372516855757 81560218662254764693820909)
          ·
            refine ⟨30585081998345536760182841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81560218662254764693820909 30585081998345536760182841)
            ·
              refine ⟨22938811498759152570137131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30585081998345536760182841 22938811498759152570137131)
              ·
                refine ⟨34408217248138728855205697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22938811498759152570137131 34408217248138728855205697)
                ·
                  refine ⟨25806162936104046641404273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34408217248138728855205697 25806162936104046641404273)
                  ·
                    refine ⟨19354622202078034981053205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25806162936104046641404273 19354622202078034981053205)
                    ·
                      refine ⟨907247915722407889736869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19354622202078034981053205 907247915722407889736869)
                      ·
                        rfl

theorem cell23_1766859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 6].length) (baseStart_1766859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766859 prefixEnd_1766859 := by exact prefixLift 1766859
  have htrace : WordTrace (prefixWord ++ tailWord_1766859) baseStart_1766859 baseEnd_1766859 := by
    simpa [prefixWord, tailWord_1766859, baseEnd_1766859] using wordTrace_append hprefix tailTrace_1766859
  have hstable : (prefixWord ++ tailWord_1766859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766859).length < 2 ^ (prefixWord ++ tailWord_1766859).sum := by decide
  have hdescent : baseEnd_1766859 < baseStart_1766859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766870 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_1766870 : Nat := 118140960795 + 1766870 * 2 ^ 59
def prefixEnd_1766870 : Nat := 4983230072969 + 3 ^ 40 * 1766870 * 2
def baseEnd_1766870 : Nat := 907253564009607346699319

theorem tailTrace_1766870 : CollatzResearch.WordTrace tailWord_1766870 prefixEnd_1766870 907253564009607346699319 := by
  unfold tailWord_1766870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4027690194308701388561129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42962028739292814811318709 4027690194308701388561129)
  ·
    refine ⟨3020767645731526041420847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4027690194308701388561129 3020767645731526041420847)
    ·
      refine ⟨4531151468597289062131271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3020767645731526041420847 4531151468597289062131271)
      ·
        refine ⟨6796727202895933593196907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4531151468597289062131271 6796727202895933593196907)
        ·
          refine ⟨10195090804343900389795361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6796727202895933593196907 10195090804343900389795361)
          ·
            refine ⟨7646318103257925292346521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10195090804343900389795361 7646318103257925292346521)
            ·
              refine ⟨5734738577443443969259891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7646318103257925292346521 5734738577443443969259891)
              ·
                refine ⟨8602107866165165953889837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5734738577443443969259891 8602107866165165953889837)
                ·
                  refine ⟨3225790449811937232708689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8602107866165165953889837 3225790449811937232708689)
                  ·
                    refine ⟨2419342837358952924531517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3225790449811937232708689 2419342837358952924531517)
                    ·
                      refine ⟨907253564009607346699319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2419342837358952924531517 907253564009607346699319)
                      ·
                        rfl

theorem cell23_1766870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_1766870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766870 prefixEnd_1766870 := by exact prefixLift 1766870
  have htrace : WordTrace (prefixWord ++ tailWord_1766870) baseStart_1766870 baseEnd_1766870 := by
    simpa [prefixWord, tailWord_1766870, baseEnd_1766870] using wordTrace_append hprefix tailTrace_1766870
  have hstable : (prefixWord ++ tailWord_1766870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766870).length < 2 ^ (prefixWord ++ tailWord_1766870).sum := by decide
  have hdescent : baseEnd_1766870 < baseStart_1766870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766883 : List Nat := [1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 3]
def baseStart_1766883 : Nat := 118140960795 + 1766883 * 2 ^ 59
def prefixEnd_1766883 : Nat := 4983230072969 + 3 ^ 40 * 1766883 * 2
def baseEnd_1766883 : Nat := 907260239258115795836759

theorem tailTrace_1766883 : CollatzResearch.WordTrace tailWord_1766883 prefixEnd_1766883 907260239258115795836759 := by
  unfold tailWord_1766883
  simp only [CollatzResearch.WordTrace]
  refine ⟨64443517257892125437201303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42962344838594750291467535 64443517257892125437201303)
  ·
    refine ⟨96665275886838188155801955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64443517257892125437201303 96665275886838188155801955)
    ·
      refine ⟨144997913830257282233702933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96665275886838188155801955 144997913830257282233702933)
      ·
        refine ⟨6796777210793310104704825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 144997913830257282233702933 6796777210793310104704825)
        ·
          refine ⟨5097582908094982578528619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6796777210793310104704825 5097582908094982578528619)
          ·
            refine ⟨7646374362142473867792929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5097582908094982578528619 7646374362142473867792929)
            ·
              refine ⟨5734780771606855400844697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7646374362142473867792929 5734780771606855400844697)
              ·
                refine ⟨4301085578705141550633523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5734780771606855400844697 4301085578705141550633523)
                ·
                  refine ⟨6451628368057712325950285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4301085578705141550633523 6451628368057712325950285)
                  ·
                    refine ⟨2419360638021642122231357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6451628368057712325950285 2419360638021642122231357)
                    ·
                      refine ⟨907260239258115795836759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2419360638021642122231357 907260239258115795836759)
                      ·
                        rfl

theorem cell23_1766883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_1766883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766883 prefixEnd_1766883 := by exact prefixLift 1766883
  have htrace : WordTrace (prefixWord ++ tailWord_1766883) baseStart_1766883 baseEnd_1766883 := by
    simpa [prefixWord, tailWord_1766883, baseEnd_1766883] using wordTrace_append hprefix tailTrace_1766883
  have hstable : (prefixWord ++ tailWord_1766883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766883).length < 2 ^ (prefixWord ++ tailWord_1766883).sum := by decide
  have hdescent : baseEnd_1766883 < baseStart_1766883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766887 : List Nat := [1, 1, 5, 2, 1, 4, 2, 1, 1, 2, 3]
def baseStart_1766887 : Nat := 118140960795 + 1766887 * 2 ^ 59
def prefixEnd_1766887 : Nat := 4983230072969 + 3 ^ 40 * 1766887 * 2
def baseEnd_1766887 : Nat := 907262293180733780186741

theorem tailTrace_1766887 : CollatzResearch.WordTrace tailWord_1766887 prefixEnd_1766887 907262293180733780186741 := by
  unfold tailWord_1766887
  simp only [CollatzResearch.WordTrace]
  refine ⟨64443663149877634120346915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42962442099918422746897943 64443663149877634120346915)
  ·
    refine ⟨96665494724816451180520373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64443663149877634120346915 96665494724816451180520373)
    ·
      refine ⟨9062390130451542298173785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96665494724816451180520373 9062390130451542298173785)
      ·
        refine ⟨6796792597838656723630339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9062390130451542298173785 6796792597838656723630339)
        ·
          refine ⟨10195188896757985085445509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6796792597838656723630339 10195188896757985085445509)
          ·
            refine ⟨1911597918142122203521033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10195188896757985085445509 1911597918142122203521033)
            ·
              refine ⟨1433698438606591652640775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1911597918142122203521033 1433698438606591652640775)
              ·
                refine ⟨2150547657909887478961163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1433698438606591652640775 2150547657909887478961163)
                ·
                  refine ⟨3225821486864831218441745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2150547657909887478961163 3225821486864831218441745)
                  ·
                    refine ⟨2419366115148623413831309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3225821486864831218441745 2419366115148623413831309)
                    ·
                      refine ⟨907262293180733780186741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2419366115148623413831309 907262293180733780186741)
                      ·
                        rfl

theorem cell23_1766887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_1766887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766887 prefixEnd_1766887 := by exact prefixLift 1766887
  have htrace : WordTrace (prefixWord ++ tailWord_1766887) baseStart_1766887 baseEnd_1766887 := by
    simpa [prefixWord, tailWord_1766887, baseEnd_1766887] using wordTrace_append hprefix tailTrace_1766887
  have hstable : (prefixWord ++ tailWord_1766887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766887).length < 2 ^ (prefixWord ++ tailWord_1766887).sum := by decide
  have hdescent : baseEnd_1766887 < baseStart_1766887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766940 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 6, 2, 2]
def baseStart_1766940 : Nat := 118140960795 + 1766940 * 2 ^ 59
def prefixEnd_1766940 : Nat := 4983230072969 + 3 ^ 40 * 1766940 * 2
def baseEnd_1766940 : Nat := 907289507655422072823997

theorem tailTrace_1766940 : CollatzResearch.WordTrace tailWord_1766940 prefixEnd_1766940 907289507655422072823997 := by
  unfold tailWord_1766940
  simp only [CollatzResearch.WordTrace]
  refine ⟨32222798109342812086013137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42963730812457082781350849 32222798109342812086013137)
  ·
    refine ⟨24167098582007109064509853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32222798109342812086013137 24167098582007109064509853)
    ·
      refine ⟨9062661968252665899191195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24167098582007109064509853 9062661968252665899191195)
      ·
        refine ⟨13593992952378998848786793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9062661968252665899191195 13593992952378998848786793)
        ·
          refine ⟨10195494714284249136590095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13593992952378998848786793 10195494714284249136590095)
          ·
            refine ⟨15293242071426373704885143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10195494714284249136590095 15293242071426373704885143)
            ·
              refine ⟨22939863107139560557327715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15293242071426373704885143 22939863107139560557327715)
              ·
                refine ⟨34409794660709340835991573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22939863107139560557327715 34409794660709340835991573)
                ·
                  refine ⟨1612959124720750351687105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34409794660709340835991573 1612959124720750351687105)
                  ·
                    refine ⟨1209719343540562763765329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1612959124720750351687105 1209719343540562763765329)
                    ·
                      refine ⟨907289507655422072823997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1209719343540562763765329 907289507655422072823997)
                      ·
                        rfl

theorem cell23_1766940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_1766940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766940 prefixEnd_1766940 := by exact prefixLift 1766940
  have htrace : WordTrace (prefixWord ++ tailWord_1766940) baseStart_1766940 baseEnd_1766940 := by
    simpa [prefixWord, tailWord_1766940, baseEnd_1766940] using wordTrace_append hprefix tailTrace_1766940
  have hstable : (prefixWord ++ tailWord_1766940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766940).length < 2 ^ (prefixWord ++ tailWord_1766940).sum := by decide
  have hdescent : baseEnd_1766940 < baseStart_1766940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766946 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 9]
def baseStart_1766946 : Nat := 118140960795 + 1766946 * 2 ^ 59
def prefixEnd_1766946 : Nat := 4983230072969 + 3 ^ 40 * 1766946 * 2
def baseEnd_1766946 : Nat := 100810287615483227705441

theorem tailTrace_1766946 : CollatzResearch.WordTrace tailWord_1766946 prefixEnd_1766946 100810287615483227705441 := by
  unfold tailWord_1766946
  simp only [CollatzResearch.WordTrace]
  refine ⟨16111453764165971799186173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42963876704442591464496461 16111453764165971799186173)
  ·
    refine ⟨6041795161562239424694815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16111453764165971799186173 6041795161562239424694815)
    ·
      refine ⟨9062692742343359137042223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6041795161562239424694815 9062692742343359137042223)
      ·
        refine ⟨13594039113515038705563335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9062692742343359137042223 13594039113515038705563335)
        ·
          refine ⟨20391058670272558058345003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13594039113515038705563335 20391058670272558058345003)
          ·
            refine ⟨30586588005408837087517505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20391058670272558058345003 30586588005408837087517505)
            ·
              refine ⟨22939941004056627815638129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30586588005408837087517505 22939941004056627815638129)
              ·
                refine ⟨17204955753042470861728597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22939941004056627815638129 17204955753042470861728597)
                ·
                  refine ⟨100810287615483227705441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17204955753042470861728597 100810287615483227705441)
                  ·
                    rfl

theorem cell23_1766946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_1766946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766946 prefixEnd_1766946 := by exact prefixLift 1766946
  have htrace : WordTrace (prefixWord ++ tailWord_1766946) baseStart_1766946 baseEnd_1766946 := by
    simpa [prefixWord, tailWord_1766946, baseEnd_1766946] using wordTrace_append hprefix tailTrace_1766946
  have hstable : (prefixWord ++ tailWord_1766946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766946).length < 2 ^ (prefixWord ++ tailWord_1766946).sum := by decide
  have hdescent : baseEnd_1766946 < baseStart_1766946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766963 : List Nat := [1, 1, 1, 2, 4, 5, 1, 1, 7]
def baseStart_1766963 : Nat := 118140960795 + 1766963 * 2 ^ 59
def prefixEnd_1766963 : Nat := 4983230072969 + 3 ^ 40 * 1766963 * 2
def baseEnd_1766963 : Nat := 100811257523386164759599

theorem tailTrace_1766963 : CollatzResearch.WordTrace tailWord_1766963 prefixEnd_1766963 100811257523386164759599 := by
  unfold tailWord_1766963
  simp only [CollatzResearch.WordTrace]
  refine ⟨64446435097602299100113543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42964290065068199400075695 64446435097602299100113543)
  ·
    refine ⟨96669652646403448650170315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64446435097602299100113543 96669652646403448650170315)
    ·
      refine ⟨145004478969605172975255473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96669652646403448650170315 145004478969605172975255473)
      ·
        refine ⟨108753359227203879731441605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145004478969605172975255473 108753359227203879731441605)
        ·
          refine ⟨20391254855100727449645301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108753359227203879731441605 20391254855100727449645301)
          ·
            refine ⟨1911680142665693198404247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20391254855100727449645301 1911680142665693198404247)
            ·
              refine ⟨2867520213998539797606371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1911680142665693198404247 2867520213998539797606371)
              ·
                refine ⟨4301280320997809696409557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2867520213998539797606371 4301280320997809696409557)
                ·
                  refine ⟨100811257523386164759599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4301280320997809696409557 100811257523386164759599)
                  ·
                    rfl

theorem cell23_1766963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 7].length) (baseStart_1766963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766963 prefixEnd_1766963 := by exact prefixLift 1766963
  have htrace : WordTrace (prefixWord ++ tailWord_1766963) baseStart_1766963 baseEnd_1766963 := by
    simpa [prefixWord, tailWord_1766963, baseEnd_1766963] using wordTrace_append hprefix tailTrace_1766963
  have hstable : (prefixWord ++ tailWord_1766963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766963).length < 2 ^ (prefixWord ++ tailWord_1766963).sum := by decide
  have hdescent : baseEnd_1766963 < baseStart_1766963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766976 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 6, 5]
def baseStart_1766976 : Nat := 118140960795 + 1766976 * 2 ^ 59
def prefixEnd_1766976 : Nat := 4983230072969 + 3 ^ 40 * 1766976 * 2
def baseEnd_1766976 : Nat := 302435997652994643991277

theorem tailTrace_1766976 : CollatzResearch.WordTrace tailWord_1766976 prefixEnd_1766976 302435997652994643991277 := by
  unfold tailWord_1766976
  simp only [CollatzResearch.WordTrace]
  refine ⟨32223454623277601160168391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42964606164370134880224521 32223454623277601160168391)
  ·
    refine ⟨48335181934916401740252587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32223454623277601160168391 48335181934916401740252587)
    ·
      refine ⟨72502772902374602610378881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48335181934916401740252587 72502772902374602610378881)
      ·
        refine ⟨54377079676780951957784161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72502772902374602610378881 54377079676780951957784161)
        ·
          refine ⟨40782809757585713968338121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54377079676780951957784161 40782809757585713968338121)
          ·
            refine ⟨30587107318189285476253591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40782809757585713968338121 30587107318189285476253591)
            ·
              refine ⟨45880660977283928214380387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30587107318189285476253591 45880660977283928214380387)
              ·
                refine ⟨68820991465925892321570581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45880660977283928214380387 68820991465925892321570581)
                ·
                  refine ⟨3225983974965276202573621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68820991465925892321570581 3225983974965276202573621)
                  ·
                    refine ⟨302435997652994643991277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3225983974965276202573621 302435997652994643991277)
                    ·
                      rfl

theorem cell23_1766976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 6, 5].length) (baseStart_1766976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766976 prefixEnd_1766976 := by exact prefixLift 1766976
  have htrace : WordTrace (prefixWord ++ tailWord_1766976) baseStart_1766976 baseEnd_1766976 := by
    simpa [prefixWord, tailWord_1766976, baseEnd_1766976] using wordTrace_append hprefix tailTrace_1766976
  have hstable : (prefixWord ++ tailWord_1766976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766976).length < 2 ^ (prefixWord ++ tailWord_1766976).sum := by decide
  have hdescent : baseEnd_1766976 < baseStart_1766976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766986 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_1766986 : Nat := 118140960795 + 1766986 * 2 ^ 59
def prefixEnd_1766986 : Nat := 4983230072969 + 3 ^ 40 * 1766986 * 2
def baseEnd_1766986 : Nat := 907313127765528892848785

theorem tailTrace_1766986 : CollatzResearch.WordTrace tailWord_1766986 prefixEnd_1766986 907313127765528892848785 := by
  unfold tailWord_1766986
  simp only [CollatzResearch.WordTrace]
  refine ⟨16111818494129743507050203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42964849317679316018800541 16111818494129743507050203)
  ·
    refine ⟨24167727741194615260575305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16111818494129743507050203 24167727741194615260575305)
    ·
      refine ⟨18125795805895961445431479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24167727741194615260575305 18125795805895961445431479)
      ·
        refine ⟨27188693708843942168147219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18125795805895961445431479 27188693708843942168147219)
        ·
          refine ⟨40783040563265913252220829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27188693708843942168147219 40783040563265913252220829)
          ·
            refine ⟨15293640211224717469582811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40783040563265913252220829 15293640211224717469582811)
            ·
              refine ⟨22940460316837076204374217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15293640211224717469582811 22940460316837076204374217)
              ·
                refine ⟨17205345237627807153280663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22940460316837076204374217 17205345237627807153280663)
                ·
                  refine ⟨25808017856441710729920995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17205345237627807153280663 25808017856441710729920995)
                  ·
                    refine ⟨38712026784662566094881493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25808017856441710729920995 38712026784662566094881493)
                    ·
                      refine ⟨907313127765528892848785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38712026784662566094881493 907313127765528892848785)
                      ·
                        rfl

theorem cell23_1766986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_1766986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766986 prefixEnd_1766986 := by exact prefixLift 1766986
  have htrace : WordTrace (prefixWord ++ tailWord_1766986) baseStart_1766986 baseEnd_1766986 := by
    simpa [prefixWord, tailWord_1766986, baseEnd_1766986] using wordTrace_append hprefix tailTrace_1766986
  have hstable : (prefixWord ++ tailWord_1766986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766986).length < 2 ^ (prefixWord ++ tailWord_1766986).sum := by decide
  have hdescent : baseEnd_1766986 < baseStart_1766986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766993 : List Nat := [1, 2, 2, 1, 3, 2, 4, 1, 2, 5]
def baseStart_1766993 : Nat := 118140960795 + 1766993 * 2 ^ 59
def prefixEnd_1766993 : Nat := 4983230072969 + 3 ^ 40 * 1766993 * 2
def baseEnd_1766993 : Nat := 302438907376703455153751

theorem tailTrace_1766993 : CollatzResearch.WordTrace tailWord_1766993 prefixEnd_1766993 302438907376703455153751 := by
  unfold tailWord_1766993
  simp only [CollatzResearch.WordTrace]
  refine ⟨64447529287493614223705633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42965019524995742815803755 64447529287493614223705633)
  ·
    refine ⟨48335646965620210667779225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64447529287493614223705633 48335646965620210667779225)
    ·
      refine ⟨36251735224215158000834419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48335646965620210667779225 36251735224215158000834419)
      ·
        refine ⟨54377602836322737001251629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36251735224215158000834419 54377602836322737001251629)
        ·
          refine ⟨20391601063621026375469361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54377602836322737001251629 20391601063621026375469361)
          ·
            refine ⟨15293700797715769781602021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20391601063621026375469361 15293700797715769781602021)
            ·
              refine ⟨2867568899571706834050379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15293700797715769781602021 2867568899571706834050379)
              ·
                refine ⟨4301353349357560251075569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2867568899571706834050379 4301353349357560251075569)
                ·
                  refine ⟨3226015012018170188306677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4301353349357560251075569 3226015012018170188306677)
                  ·
                    refine ⟨302438907376703455153751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3226015012018170188306677 302438907376703455153751)
                    ·
                      rfl

theorem cell23_1766993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_1766993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1766993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1766993 prefixEnd_1766993 := by exact prefixLift 1766993
  have htrace : WordTrace (prefixWord ++ tailWord_1766993) baseStart_1766993 baseEnd_1766993 := by
    simpa [prefixWord, tailWord_1766993, baseEnd_1766993] using wordTrace_append hprefix tailTrace_1766993
  have hstable : (prefixWord ++ tailWord_1766993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766993).length < 2 ^ (prefixWord ++ tailWord_1766993).sum := by decide
  have hdescent : baseEnd_1766993 < baseStart_1766993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767023 : List Nat := [1, 1, 2, 1, 3, 2, 1, 5, 3, 4]
def baseStart_1767023 : Nat := 118140960795 + 1767023 * 2 ^ 59
def prefixEnd_1767023 : Nat := 4983230072969 + 3 ^ 40 * 1767023 * 2
def baseEnd_1767023 : Nat := 302444042183248416028705

theorem tailTrace_1767023 : CollatzResearch.WordTrace tailWord_1767023 prefixEnd_1767023 302444042183248416028705 := by
  unfold tailWord_1767023
  simp only [CollatzResearch.WordTrace]
  refine ⟨64448623477384929347297723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42965748984923286231531815 64448623477384929347297723)
  ·
    refine ⟨96672935216077394020946585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64448623477384929347297723 96672935216077394020946585)
    ·
      refine ⟨72504701412058045515709939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96672935216077394020946585 72504701412058045515709939)
      ·
        refine ⟨108757052118087068273564909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72504701412058045515709939 108757052118087068273564909)
        ·
          refine ⟨40783894544282650602586841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108757052118087068273564909 40783894544282650602586841)
          ·
            refine ⟨30587920908211987951940131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40783894544282650602586841 30587920908211987951940131)
            ·
              refine ⟨45881881362317981927910197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30587920908211987951940131 45881881362317981927910197)
              ·
                refine ⟨4301426377717310805741581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45881881362317981927910197 4301426377717310805741581)
                ·
                  refine ⟨1613034891643991552153093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4301426377717310805741581 1613034891643991552153093)
                  ·
                    refine ⟨302444042183248416028705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1613034891643991552153093 302444042183248416028705)
                    ·
                      rfl

theorem cell23_1767023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 4].length) (baseStart_1767023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767023 prefixEnd_1767023 := by exact prefixLift 1767023
  have htrace : WordTrace (prefixWord ++ tailWord_1767023) baseStart_1767023 baseEnd_1767023 := by
    simpa [prefixWord, tailWord_1767023, baseEnd_1767023] using wordTrace_append hprefix tailTrace_1767023
  have hstable : (prefixWord ++ tailWord_1767023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767023).length < 2 ^ (prefixWord ++ tailWord_1767023).sum := by decide
  have hdescent : baseEnd_1767023 < baseStart_1767023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767033 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 1, 4, 3]
def baseStart_1767033 : Nat := 118140960795 + 1767033 * 2 ^ 59
def prefixEnd_1767033 : Nat := 4983230072969 + 3 ^ 40 * 1767033 * 2
def baseEnd_1767033 : Nat := 907337261356290208961069

theorem tailTrace_1767033 : CollatzResearch.WordTrace tailWord_1767033 prefixEnd_1767033 907337261356290208961069 := by
  unfold tailWord_1767033
  simp only [CollatzResearch.WordTrace]
  refine ⟨64448988207348701055161753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42965992138232467370107835 64448988207348701055161753)
  ·
    refine ⟨48336741155511525791371315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64448988207348701055161753 48336741155511525791371315)
    ·
      refine ⟨72505111733267288687056973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48336741155511525791371315 72505111733267288687056973)
      ·
        refine ⟨27189416899975233257646365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72505111733267288687056973 27189416899975233257646365)
        ·
          refine ⟨10196031337490712471617387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27189416899975233257646365 10196031337490712471617387)
          ·
            refine ⟨15294047006236068707426081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10196031337490712471617387 15294047006236068707426081)
            ·
              refine ⟨11470535254677051530569561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15294047006236068707426081 11470535254677051530569561)
              ·
                refine ⟨8602901441007788647927171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11470535254677051530569561 8602901441007788647927171)
                ·
                  refine ⟨12904352161511682971890757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8602901441007788647927171 12904352161511682971890757)
                  ·
                    refine ⟨2419566030283440557229517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12904352161511682971890757 2419566030283440557229517)
                    ·
                      refine ⟨907337261356290208961069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2419566030283440557229517 907337261356290208961069)
                      ·
                        rfl

theorem cell23_1767033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_1767033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767033 prefixEnd_1767033 := by exact prefixLift 1767033
  have htrace : WordTrace (prefixWord ++ tailWord_1767033) baseStart_1767033 baseEnd_1767033 := by
    simpa [prefixWord, tailWord_1767033, baseEnd_1767033] using wordTrace_append hprefix tailTrace_1767033
  have hstable : (prefixWord ++ tailWord_1767033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767033).length < 2 ^ (prefixWord ++ tailWord_1767033).sum := by decide
  have hdescent : baseEnd_1767033 < baseStart_1767033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767036 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 10]
def baseStart_1767036 : Nat := 118140960795 + 1767036 * 2 ^ 59
def prefixEnd_1767036 : Nat := 4983230072969 + 3 ^ 40 * 1767036 * 2
def baseEnd_1767036 : Nat := 100815422422028188580395

theorem tailTrace_1767036 : CollatzResearch.WordTrace tailWord_1767036 prefixEnd_1767036 100815422422028188580395 := by
  unfold tailWord_1767036
  simp only [CollatzResearch.WordTrace]
  refine ⟨32224548813168916283760481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42966065084225221711680641 32224548813168916283760481)
  ·
    refine ⟨24168411609876687212820361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32224548813168916283760481 24168411609876687212820361)
    ·
      refine ⟨18126308707407515409615271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24168411609876687212820361 18126308707407515409615271)
      ·
        refine ⟨27189463061111273114422907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18126308707407515409615271 27189463061111273114422907)
        ·
          refine ⟨40784194591666909671634361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27189463061111273114422907 40784194591666909671634361)
          ·
            refine ⟨30588145943750182253725771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40784194591666909671634361 30588145943750182253725771)
            ·
              refine ⟨45882218915625273380588657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30588145943750182253725771 45882218915625273380588657)
              ·
                refine ⟨34411664186718955035441493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45882218915625273380588657 34411664186718955035441493)
                ·
                  refine ⟨100815422422028188580395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 34411664186718955035441493 100815422422028188580395)
                  ·
                    rfl

theorem cell23_1767036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 10].length) (baseStart_1767036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767036 prefixEnd_1767036 := by exact prefixLift 1767036
  have htrace : WordTrace (prefixWord ++ tailWord_1767036) baseStart_1767036 baseEnd_1767036 := by
    simpa [prefixWord, tailWord_1767036, baseEnd_1767036] using wordTrace_append hprefix tailTrace_1767036
  have hstable : (prefixWord ++ tailWord_1767036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767036).length < 2 ^ (prefixWord ++ tailWord_1767036).sum := by decide
  have hdescent : baseEnd_1767036 < baseStart_1767036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767050 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 1, 4, 3]
def baseStart_1767050 : Nat := 118140960795 + 1767050 * 2 ^ 59
def prefixEnd_1767050 : Nat := 4983230072969 + 3 ^ 40 * 1767050 * 2
def baseEnd_1767050 : Nat := 907345990527416642448491

theorem tailTrace_1767050 : CollatzResearch.WordTrace tailWord_1767050 prefixEnd_1767050 907345990527416642448491 := by
  unfold tailWord_1767050
  simp only [CollatzResearch.WordTrace]
  refine ⟨16112402062071778239632651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42966405498858075305687069 16112402062071778239632651)
  ·
    refine ⟨24168603093107667359448977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16112402062071778239632651 24168603093107667359448977)
    ·
      refine ⟨18126452319830750519586733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24168603093107667359448977 18126452319830750519586733)
      ·
        refine ⟨6797419619936531444845025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18126452319830750519586733 6797419619936531444845025)
        ·
          refine ⟨5098064714952398583633769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6797419619936531444845025 5098064714952398583633769)
          ·
            refine ⟨3823548536214298937725327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5098064714952398583633769 3823548536214298937725327)
            ·
              refine ⟨5735322804321448406587991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3823548536214298937725327 5735322804321448406587991)
              ·
                refine ⟨8602984206482172609881987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5735322804321448406587991 8602984206482172609881987)
                ·
                  refine ⟨12904476309723258914822981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8602984206482172609881987 12904476309723258914822981)
                  ·
                    refine ⟨2419589308073111046529309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12904476309723258914822981 2419589308073111046529309)
                    ·
                      refine ⟨907345990527416642448491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2419589308073111046529309 907345990527416642448491)
                      ·
                        rfl

theorem cell23_1767050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_1767050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767050 prefixEnd_1767050 := by exact prefixLift 1767050
  have htrace : WordTrace (prefixWord ++ tailWord_1767050) baseStart_1767050 baseEnd_1767050 := by
    simpa [prefixWord, tailWord_1767050, baseEnd_1767050] using wordTrace_append hprefix tailTrace_1767050
  have hstable : (prefixWord ++ tailWord_1767050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767050).length < 2 ^ (prefixWord ++ tailWord_1767050).sum := by decide
  have hdescent : baseEnd_1767050 < baseStart_1767050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767056 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 6]
def baseStart_1767056 : Nat := 118140960795 + 1767056 * 2 ^ 59
def prefixEnd_1767056 : Nat := 4983230072969 + 3 ^ 40 * 1767056 * 2
def baseEnd_1767056 : Nat := 907349071411343618973463

theorem tailTrace_1767056 : CollatzResearch.WordTrace tailWord_1767056 prefixEnd_1767056 907349071411343618973463 := by
  unfold tailWord_1767056
  simp only [CollatzResearch.WordTrace]
  refine ⟨32224913543132687991624511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42966551390843583988832681 32224913543132687991624511)
  ·
    refine ⟨48337370314699031987436767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32224913543132687991624511 48337370314699031987436767)
    ·
      refine ⟨72506055472048547981155151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48337370314699031987436767 72506055472048547981155151)
      ·
        refine ⟨108759083208072821971732727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72506055472048547981155151 108759083208072821971732727)
        ·
          refine ⟨163138624812109232957599091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108759083208072821971732727 163138624812109232957599091)
          ·
            refine ⟨244707937218163849436398637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163138624812109232957599091 244707937218163849436398637)
            ·
              refine ⟨91765476456811443538649489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244707937218163849436398637 91765476456811443538649489)
              ·
                refine ⟨68824107342608582653987117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91765476456811443538649489 68824107342608582653987117)
                ·
                  refine ⟨25809040253478218495245169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68824107342608582653987117 25809040253478218495245169)
                  ·
                    refine ⟨19356780190108663871433877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25809040253478218495245169 19356780190108663871433877)
                    ·
                      refine ⟨907349071411343618973463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19356780190108663871433877 907349071411343618973463)
                      ·
                        rfl

theorem cell23_1767056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_1767056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767056 prefixEnd_1767056 := by exact prefixLift 1767056
  have htrace : WordTrace (prefixWord ++ tailWord_1767056) baseStart_1767056 baseEnd_1767056 := by
    simpa [prefixWord, tailWord_1767056, baseEnd_1767056] using wordTrace_append hprefix tailTrace_1767056
  have hstable : (prefixWord ++ tailWord_1767056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767056).length < 2 ^ (prefixWord ++ tailWord_1767056).sum := by decide
  have hdescent : baseEnd_1767056 < baseStart_1767056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767070 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 8]
def baseStart_1767070 : Nat := 118140960795 + 1767070 * 2 ^ 59
def prefixEnd_1767070 : Nat := 4983230072969 + 3 ^ 40 * 1767070 * 2
def baseEnd_1767070 : Nat := 100817362237834062688711

theorem tailTrace_1767070 : CollatzResearch.WordTrace tailWord_1767070 prefixEnd_1767070 100817362237834062688711 := by
  unfold tailWord_1767070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8056292213526832046782333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42966891805476437582839109 8056292213526832046782333)
  ·
    refine ⟨3021109580072562017543375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8056292213526832046782333 3021109580072562017543375)
    ·
      refine ⟨4531664370108843026315063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3021109580072562017543375 4531664370108843026315063)
      ·
        refine ⟨6797496555163264539472595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4531664370108843026315063 6797496555163264539472595)
        ·
          refine ⟨10196244832744896809208893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6797496555163264539472595 10196244832744896809208893)
          ·
            refine ⟨3823591812279336303453335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10196244832744896809208893 3823591812279336303453335)
            ·
              refine ⟨5735387718419004455180003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3823591812279336303453335 5735387718419004455180003)
              ·
                refine ⟨8603081577628506682770005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5735387718419004455180003 8603081577628506682770005)
                ·
                  refine ⟨100817362237834062688711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8603081577628506682770005 100817362237834062688711)
                  ·
                    rfl

theorem cell23_1767070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_1767070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767070 prefixEnd_1767070 := by exact prefixLift 1767070
  have htrace : WordTrace (prefixWord ++ tailWord_1767070) baseStart_1767070 baseEnd_1767070 := by
    simpa [prefixWord, tailWord_1767070, baseEnd_1767070] using wordTrace_append hprefix tailTrace_1767070
  have hstable : (prefixWord ++ tailWord_1767070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767070).length < 2 ^ (prefixWord ++ tailWord_1767070).sum := by decide
  have hdescent : baseEnd_1767070 < baseStart_1767070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767073 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1767073 : Nat := 118140960795 + 1767073 * 2 ^ 59
def prefixEnd_1767073 : Nat := 4983230072969 + 3 ^ 40 * 1767073 * 2
def baseEnd_1767073 : Nat := 907357800582470052460885

theorem tailTrace_1767073 : CollatzResearch.WordTrace tailWord_1767073 prefixEnd_1767073 907357800582470052460885 := by
  unfold tailWord_1767073
  simp only [CollatzResearch.WordTrace]
  refine ⟨64450447127203787886617873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42966964751469191924411915 64450447127203787886617873)
  ·
    refine ⟨48337835345402840914963405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64450447127203787886617873 48337835345402840914963405)
    ·
      refine ⟨18126688254526065343111277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48337835345402840914963405 18126688254526065343111277)
      ·
        refine ⟨6797508095447274503666729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18126688254526065343111277 6797508095447274503666729)
        ·
          refine ⟨5098131071585455877750047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6797508095447274503666729 5098131071585455877750047)
          ·
            refine ⟨7647196607378183816625071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5098131071585455877750047 7647196607378183816625071)
            ·
              refine ⟨11470794911067275724937607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7647196607378183816625071 11470794911067275724937607)
              ·
                refine ⟨17206192366600913587406411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11470794911067275724937607 17206192366600913587406411)
                ·
                  refine ⟨25809288549901370381109617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17206192366600913587406411 25809288549901370381109617)
                  ·
                    refine ⟨19356966412426027785832213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25809288549901370381109617 19356966412426027785832213)
                    ·
                      refine ⟨907357800582470052460885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19356966412426027785832213 907357800582470052460885)
                      ·
                        rfl

theorem cell23_1767073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1767073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767073 prefixEnd_1767073 := by exact prefixLift 1767073
  have htrace : WordTrace (prefixWord ++ tailWord_1767073) baseStart_1767073 baseEnd_1767073 := by
    simpa [prefixWord, tailWord_1767073, baseEnd_1767073] using wordTrace_append hprefix tailTrace_1767073
  have hstable : (prefixWord ++ tailWord_1767073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767073).length < 2 ^ (prefixWord ++ tailWord_1767073).sum := by decide
  have hdescent : baseEnd_1767073 < baseStart_1767073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767074 : List Nat := [3, 3, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_1767074 : Nat := 118140960795 + 1767074 * 2 ^ 59
def prefixEnd_1767074 : Nat := 4983230072969 + 3 ^ 40 * 1767074 * 2
def baseEnd_1767074 : Nat := 302452771354374849516127

theorem tailTrace_1767074 : CollatzResearch.WordTrace tailWord_1767074 prefixEnd_1767074 302452771354374849516127 := by
  unfold tailWord_1767074
  simp only [CollatzResearch.WordTrace]
  refine ⟨16112620900050041264351069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42966989066800110038269517 16112620900050041264351069)
  ·
    refine ⟨6042232837518765474131651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16112620900050041264351069 6042232837518765474131651)
    ·
      refine ⟨9063349256278148211197477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6042232837518765474131651 9063349256278148211197477)
      ·
        refine ⟨1699377985552152789599527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9063349256278148211197477 1699377985552152789599527)
        ·
          refine ⟨2549066978328229184399291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1699377985552152789599527 2549066978328229184399291)
          ·
            refine ⟨3823600467492343776598937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549066978328229184399291 3823600467492343776598937)
            ·
              refine ⟨2867700350619257832449203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3823600467492343776598937 2867700350619257832449203)
              ·
                refine ⟨4301550525928886748673805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2867700350619257832449203 4301550525928886748673805)
                ·
                  refine ⟨1613081447223332530752677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4301550525928886748673805 1613081447223332530752677)
                  ·
                    refine ⟨302452771354374849516127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1613081447223332530752677 302452771354374849516127)
                    ·
                      rfl

theorem cell23_1767074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_1767074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767074 prefixEnd_1767074 := by exact prefixLift 1767074
  have htrace : WordTrace (prefixWord ++ tailWord_1767074) baseStart_1767074 baseEnd_1767074 := by
    simpa [prefixWord, tailWord_1767074, baseEnd_1767074] using wordTrace_append hprefix tailTrace_1767074
  have hstable : (prefixWord ++ tailWord_1767074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767074).length < 2 ^ (prefixWord ++ tailWord_1767074).sum := by decide
  have hdescent : baseEnd_1767074 < baseStart_1767074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767090 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2]
def baseStart_1767090 : Nat := 118140960795 + 1767090 * 2 ^ 59
def prefixEnd_1767090 : Nat := 4983230072969 + 3 ^ 40 * 1767090 * 2
def baseEnd_1767090 : Nat := 907366529753596485948307

theorem tailTrace_1767090 : CollatzResearch.WordTrace tailWord_1767090 prefixEnd_1767090 907366529753596485948307 := by
  unfold tailWord_1767090
  simp only [CollatzResearch.WordTrace]
  refine ⟨16112766792035549947496681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42967378112094799859991149 16112766792035549947496681)
  ·
    refine ⟨12084575094026662460622511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16112766792035549947496681 12084575094026662460622511)
    ·
      refine ⟨18126862641039993690933767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12084575094026662460622511 18126862641039993690933767)
      ·
        refine ⟨27190293961559990536400651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18126862641039993690933767 27190293961559990536400651)
        ·
          refine ⟨40785440942339985804600977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27190293961559990536400651 40785440942339985804600977)
          ·
            refine ⟨30589080706754989353450733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40785440942339985804600977 30589080706754989353450733)
            ·
              refine ⟨11470905265033121007544025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30589080706754989353450733 11470905265033121007544025)
              ·
                refine ⟨8603178948774840755658019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11470905265033121007544025 8603178948774840755658019)
                ·
                  refine ⟨12904768423162261133487029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8603178948774840755658019 12904768423162261133487029)
                  ·
                    refine ⟨1209822039671461981264409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12904768423162261133487029 1209822039671461981264409)
                    ·
                      refine ⟨907366529753596485948307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1209822039671461981264409 907366529753596485948307)
                      ·
                        rfl

theorem cell23_1767090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_1767090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767090 prefixEnd_1767090 := by exact prefixLift 1767090
  have htrace : WordTrace (prefixWord ++ tailWord_1767090) baseStart_1767090 baseEnd_1767090 := by
    simpa [prefixWord, tailWord_1767090, baseEnd_1767090] using wordTrace_append hprefix tailTrace_1767090
  have hstable : (prefixWord ++ tailWord_1767090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767090).length < 2 ^ (prefixWord ++ tailWord_1767090).sum := by decide
  have hdescent : baseEnd_1767090 < baseStart_1767090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767100 : List Nat := [2, 2, 2, 3, 1, 2, 1, 4, 1, 5]
def baseStart_1767100 : Nat := 118140960795 + 1767100 * 2 ^ 59
def prefixEnd_1767100 : Nat := 4983230072969 + 3 ^ 40 * 1767100 * 2
def baseEnd_1767100 : Nat := 302457221520047148941087

theorem tailTrace_1767100 : CollatzResearch.WordTrace tailWord_1767100 prefixEnd_1767100 302457221520047148941087 := by
  unfold tailWord_1767100
  simp only [CollatzResearch.WordTrace]
  refine ⟨32225715949052985748925377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42967621265403980998567169 32225715949052985748925377)
  ·
    refine ⟨24169286961789739311694033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32225715949052985748925377 24169286961789739311694033)
    ·
      refine ⟨18126965221342304483770525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24169286961789739311694033 18126965221342304483770525)
      ·
        refine ⟨6797611958003364181413947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18126965221342304483770525 6797611958003364181413947)
        ·
          refine ⟨10196417937005046272120921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6797611958003364181413947 10196417937005046272120921)
          ·
            refine ⟨7647313452753784704090691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10196417937005046272120921 7647313452753784704090691)
            ·
              refine ⟨11470970179130677056136037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7647313452753784704090691 11470970179130677056136037)
              ·
                refine ⟨2150806908587001948025507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11470970179130677056136037 2150806908587001948025507)
                ·
                  refine ⟨3226210362880502922038261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2150806908587001948025507 3226210362880502922038261)
                  ·
                    refine ⟨302457221520047148941087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3226210362880502922038261 302457221520047148941087)
                    ·
                      rfl

theorem cell23_1767100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_1767100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767100 prefixEnd_1767100 := by exact prefixLift 1767100
  have htrace : WordTrace (prefixWord ++ tailWord_1767100) baseStart_1767100 baseEnd_1767100 := by
    simpa [prefixWord, tailWord_1767100, baseEnd_1767100] using wordTrace_append hprefix tailTrace_1767100
  have hstable : (prefixWord ++ tailWord_1767100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767100).length < 2 ^ (prefixWord ++ tailWord_1767100).sum := by decide
  have hdescent : baseEnd_1767100 < baseStart_1767100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767124 : List Nat := [2, 4, 1, 3, 1, 2, 1, 2, 2, 3, 2]
def baseStart_1767124 : Nat := 118140960795 + 1767124 * 2 ^ 59
def prefixEnd_1767124 : Nat := 4983230072969 + 3 ^ 40 * 1767124 * 2
def baseEnd_1767124 : Nat := 907383988095849352923151

theorem tailTrace_1767124 : CollatzResearch.WordTrace tailWord_1767124 prefixEnd_1767124 907383988095849352923151 := by
  unfold tailWord_1767124
  simp only [CollatzResearch.WordTrace]
  refine ⟨32226153625009511798362213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42968204833346015731149617 32226153625009511798362213)
  ·
    refine ⟨6042403804689283462192915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32226153625009511798362213 6042403804689283462192915)
    ·
      refine ⟨9063605707033925193289373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6042403804689283462192915 9063605707033925193289373)
      ·
        refine ⟨3398852140137721947483515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9063605707033925193289373 3398852140137721947483515)
        ·
          refine ⟨5098278210206582921225273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3398852140137721947483515 5098278210206582921225273)
          ·
            refine ⟨3823708657654937190918955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5098278210206582921225273 3823708657654937190918955)
            ·
              refine ⟨5735562986482405786378433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3823708657654937190918955 5735562986482405786378433)
              ·
                refine ⟨4301672239861804339783825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5735562986482405786378433 4301672239861804339783825)
                ·
                  refine ⟨3226254179896353254837869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4301672239861804339783825 3226254179896353254837869)
                  ·
                    refine ⟨1209845317461132470564201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3226254179896353254837869 1209845317461132470564201)
                    ·
                      refine ⟨907383988095849352923151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1209845317461132470564201 907383988095849352923151)
                      ·
                        rfl

theorem cell23_1767124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_1767124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767124 prefixEnd_1767124 := by exact prefixLift 1767124
  have htrace : WordTrace (prefixWord ++ tailWord_1767124) baseStart_1767124 baseEnd_1767124 := by
    simpa [prefixWord, tailWord_1767124, baseEnd_1767124] using wordTrace_append hprefix tailTrace_1767124
  have hstable : (prefixWord ++ tailWord_1767124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767124).length < 2 ^ (prefixWord ++ tailWord_1767124).sum := by decide
  have hdescent : baseEnd_1767124 < baseStart_1767124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767130 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 4, 4]
def baseStart_1767130 : Nat := 118140960795 + 1767130 * 2 ^ 59
def prefixEnd_1767130 : Nat := 4983230072969 + 3 ^ 40 * 1767130 * 2
def baseEnd_1767130 : Nat := 302462356326592109816041

theorem tailTrace_1767130 : CollatzResearch.WordTrace tailWord_1767130 prefixEnd_1767130 302462356326592109816041 := by
  unfold tailWord_1767130
  simp only [CollatzResearch.WordTrace]
  refine ⟨16113131521999321655360711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42968350725331524414295229 16113131521999321655360711)
  ·
    refine ⟨24169697282998982483041067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16113131521999321655360711 24169697282998982483041067)
    ·
      refine ⟨36254545924498473724561601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24169697282998982483041067 36254545924498473724561601)
      ·
        refine ⟨27190909443373855293421201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36254545924498473724561601 27190909443373855293421201)
        ·
          refine ⟨20393182082530391470065901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27190909443373855293421201 20393182082530391470065901)
          ·
            refine ⟨7647443280948896801274713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20393182082530391470065901 7647443280948896801274713)
            ·
              refine ⟨5735582460711672600956035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7647443280948896801274713 5735582460711672600956035)
              ·
                refine ⟨8603373691067508901434053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5735582460711672600956035 8603373691067508901434053)
                ·
                  refine ⟨1613132567075157919018885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8603373691067508901434053 1613132567075157919018885)
                  ·
                    refine ⟨302462356326592109816041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1613132567075157919018885 302462356326592109816041)
                    ·
                      rfl

theorem cell23_1767130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 4, 4].length) (baseStart_1767130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767130 prefixEnd_1767130 := by exact prefixLift 1767130
  have htrace : WordTrace (prefixWord ++ tailWord_1767130) baseStart_1767130 baseEnd_1767130 := by
    simpa [prefixWord, tailWord_1767130, baseEnd_1767130] using wordTrace_append hprefix tailTrace_1767130
  have hstable : (prefixWord ++ tailWord_1767130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767130).length < 2 ^ (prefixWord ++ tailWord_1767130).sum := by decide
  have hdescent : baseEnd_1767130 < baseStart_1767130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767140 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 3, 2, 3]
def baseStart_1767140 : Nat := 118140960795 + 1767140 * 2 ^ 59
def prefixEnd_1767140 : Nat := 4983230072969 + 3 ^ 40 * 1767140 * 2
def baseEnd_1767140 : Nat := 907392203786321290323077

theorem tailTrace_1767140 : CollatzResearch.WordTrace tailWord_1767140 prefixEnd_1767140 907392203786321290323077 := by
  unfold tailWord_1767140
  simp only [CollatzResearch.WordTrace]
  refine ⟨32226445408980529164653437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42968593878640705552871249 32226445408980529164653437)
  ·
    refine ⟨12084917028367698436745039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32226445408980529164653437 12084917028367698436745039)
    ·
      refine ⟨18127375542551547655117559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12084917028367698436745039 18127375542551547655117559)
      ·
        refine ⟨27191063313827321482676339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18127375542551547655117559 27191063313827321482676339)
        ·
          refine ⟨40786594970740982224014509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27191063313827321482676339 40786594970740982224014509)
          ·
            refine ⟨15294973114027868334005441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40786594970740982224014509 15294973114027868334005441)
            ·
              refine ⟨11471229835520901250504081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15294973114027868334005441 11471229835520901250504081)
              ·
                refine ⟨8603422376640675937878061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11471229835520901250504081 8603422376640675937878061)
                ·
                  refine ⟨3226283391240253476704273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8603422376640675937878061 3226283391240253476704273)
                  ·
                    refine ⟨2419712543430190107528205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3226283391240253476704273 2419712543430190107528205)
                    ·
                      refine ⟨907392203786321290323077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2419712543430190107528205 907392203786321290323077)
                      ·
                        rfl

theorem cell23_1767140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_1767140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767140 prefixEnd_1767140 := by exact prefixLift 1767140
  have htrace : WordTrace (prefixWord ++ tailWord_1767140) baseStart_1767140 baseEnd_1767140 := by
    simpa [prefixWord, tailWord_1767140, baseEnd_1767140] using wordTrace_append hprefix tailTrace_1767140
  have hstable : (prefixWord ++ tailWord_1767140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767140).length < 2 ^ (prefixWord ++ tailWord_1767140).sum := by decide
  have hdescent : baseEnd_1767140 < baseStart_1767140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767147 : List Nat := [1, 1, 1, 1, 2, 4, 6, 1, 2, 4]
def baseStart_1767147 : Nat := 118140960795 + 1767147 * 2 ^ 59
def prefixEnd_1767147 : Nat := 4983230072969 + 3 ^ 40 * 1767147 * 2
def baseEnd_1767147 : Nat := 302465266050300920978515

theorem tailTrace_1767147 : CollatzResearch.WordTrace tailWord_1767147 prefixEnd_1767147 302465266050300920978515 := by
  unfold tailWord_1767147
  simp only [CollatzResearch.WordTrace]
  refine ⟨64453146128935698524811695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42968764085957132349874463 64453146128935698524811695)
  ·
    refine ⟨96679719193403547787217543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64453146128935698524811695 96679719193403547787217543)
    ·
      refine ⟨145019578790105321680826315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96679719193403547787217543 145019578790105321680826315)
      ·
        refine ⟨217529368185157982521239473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145019578790105321680826315 217529368185157982521239473)
        ·
          refine ⟨163147026138868486890929605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217529368185157982521239473 163147026138868486890929605)
          ·
            refine ⟨30590067401037841292049301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163147026138868486890929605 30590067401037841292049301)
            ·
              refine ⟨1433909409423648810564811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30590067401037841292049301 1433909409423648810564811)
              ·
                refine ⟨2150864114135473215847217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1433909409423648810564811 2150864114135473215847217)
                ·
                  refine ⟨1613148085601604911885413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2150864114135473215847217 1613148085601604911885413)
                  ·
                    refine ⟨302465266050300920978515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1613148085601604911885413 302465266050300920978515)
                    ·
                      rfl

theorem cell23_1767147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 2, 4].length) (baseStart_1767147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767147 prefixEnd_1767147 := by exact prefixLift 1767147
  have htrace : WordTrace (prefixWord ++ tailWord_1767147) baseStart_1767147 baseEnd_1767147 := by
    simpa [prefixWord, tailWord_1767147, baseEnd_1767147] using wordTrace_append hprefix tailTrace_1767147
  have hstable : (prefixWord ++ tailWord_1767147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767147).length < 2 ^ (prefixWord ++ tailWord_1767147).sum := by decide
  have hdescent : baseEnd_1767147 < baseStart_1767147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767150 : List Nat := [4, 1, 2, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_1767150 : Nat := 118140960795 + 1767150 * 2 ^ 59
def prefixEnd_1767150 : Nat := 4983230072969 + 3 ^ 40 * 1767150 * 2
def baseEnd_1767150 : Nat := 907397338592866251198031

theorem tailTrace_1767150 : CollatzResearch.WordTrace tailWord_1767150 prefixEnd_1767150 907397338592866251198031 := by
  unfold tailWord_1767150
  simp only [CollatzResearch.WordTrace]
  refine ⟨8056656943490603754646363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42968837031949886691447269 8056656943490603754646363)
  ·
    refine ⟨12084985415235905631969545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8056656943490603754646363 12084985415235905631969545)
    ·
      refine ⟨9063739061426929223977159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12084985415235905631969545 9063739061426929223977159)
      ·
        refine ⟨13595608592140393835965739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9063739061426929223977159 13595608592140393835965739)
        ·
          refine ⟨20393412888210590753948609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13595608592140393835965739 20393412888210590753948609)
          ·
            refine ⟨15295059666157943065461457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20393412888210590753948609 15295059666157943065461457)
            ·
              refine ⟨11471294749618457299096093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15295059666157943065461457 11471294749618457299096093)
              ·
                refine ⟨4301735531106921487161035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11471294749618457299096093 4301735531106921487161035)
                ·
                  refine ⟨6452603296660382230741553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4301735531106921487161035 6452603296660382230741553)
                  ·
                    refine ⟨4839452472495286673056165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6452603296660382230741553 4839452472495286673056165)
                    ·
                      refine ⟨907397338592866251198031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4839452472495286673056165 907397338592866251198031)
                      ·
                        rfl

theorem cell23_1767150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_1767150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767150 prefixEnd_1767150 := by exact prefixLift 1767150
  have htrace : WordTrace (prefixWord ++ tailWord_1767150) baseStart_1767150 baseEnd_1767150 := by
    simpa [prefixWord, tailWord_1767150, baseEnd_1767150] using wordTrace_append hprefix tailTrace_1767150
  have hstable : (prefixWord ++ tailWord_1767150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767150).length < 2 ^ (prefixWord ++ tailWord_1767150).sum := by decide
  have hdescent : baseEnd_1767150 < baseStart_1767150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767203 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 1, 8]
def baseStart_1767203 : Nat := 118140960795 + 1767203 * 2 ^ 59
def prefixEnd_1767203 : Nat := 4983230072969 + 3 ^ 40 * 1767203 * 2
def baseEnd_1767203 : Nat := 302474851022518181278429

theorem tailTrace_1767203 : CollatzResearch.WordTrace tailWord_1767203 prefixEnd_1767203 302474851022518181278429 := by
  unfold tailWord_1767203
  simp only [CollatzResearch.WordTrace]
  refine ⟨64455188616732820088850263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42970125744488546725900175 64455188616732820088850263)
  ·
    refine ⟨96682782925099230133275395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64455188616732820088850263 96682782925099230133275395)
    ·
      refine ⟨145024174387648845199913093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96682782925099230133275395 145024174387648845199913093)
      ·
        refine ⟨27192032697684158474983705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145024174387648845199913093 27192032697684158474983705)
        ·
          refine ⟨20394024523263118856237779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27192032697684158474983705 20394024523263118856237779)
          ·
            refine ⟨30591036784894678284356669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20394024523263118856237779 30591036784894678284356669)
            ·
              refine ⟨11471638794335504356633751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30591036784894678284356669 11471638794335504356633751)
              ·
                refine ⟨17207458191503256534950627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11471638794335504356633751 17207458191503256534950627)
                ·
                  refine ⟨25811187287254884802425941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17207458191503256534950627 25811187287254884802425941)
                  ·
                    refine ⟨302474851022518181278429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25811187287254884802425941 302474851022518181278429)
                    ·
                      rfl

theorem cell23_1767203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 8].length) (baseStart_1767203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767203 prefixEnd_1767203 := by exact prefixLift 1767203
  have htrace : WordTrace (prefixWord ++ tailWord_1767203) baseStart_1767203 baseEnd_1767203 := by
    simpa [prefixWord, tailWord_1767203, baseEnd_1767203] using wordTrace_append hprefix tailTrace_1767203
  have hstable : (prefixWord ++ tailWord_1767203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767203).length < 2 ^ (prefixWord ++ tailWord_1767203).sum := by decide
  have hdescent : baseEnd_1767203 < baseStart_1767203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767204 : List Nat := [2, 3, 1, 3, 2, 1, 2, 3, 2, 1, 3]
def baseStart_1767204 : Nat := 118140960795 + 1767204 * 2 ^ 59
def prefixEnd_1767204 : Nat := 4983230072969 + 3 ^ 40 * 1767204 * 2
def baseEnd_1767204 : Nat := 907425066548209039922783

theorem tailTrace_1767204 : CollatzResearch.WordTrace tailWord_1767204 prefixEnd_1767204 907425066548209039922783 := by
  unfold tailWord_1767204
  simp only [CollatzResearch.WordTrace]
  refine ⟨32227612544864598629818333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42970150059819464839757777 32227612544864598629818333)
  ·
    refine ⟨12085354704324224486181875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32227612544864598629818333 12085354704324224486181875)
    ·
      refine ⟨18128032056486336729272813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12085354704324224486181875 18128032056486336729272813)
      ·
        refine ⟨6798012021182376273477305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18128032056486336729272813 6798012021182376273477305)
        ·
          refine ⟨5098509015886782205107979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6798012021182376273477305 5098509015886782205107979)
          ·
            refine ⟨7647763523830173307661969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5098509015886782205107979 7647763523830173307661969)
            ·
              refine ⟨5735822642872629980746477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7647763523830173307661969 5735822642872629980746477)
              ·
                refine ⟨2150933491077236242779929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5735822642872629980746477 2150933491077236242779929)
                ·
                  refine ⟨1613200118307927182084947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2150933491077236242779929 1613200118307927182084947)
                  ·
                    refine ⟨2419800177461890773127421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1613200118307927182084947 2419800177461890773127421)
                    ·
                      refine ⟨907425066548209039922783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2419800177461890773127421 907425066548209039922783)
                      ·
                        rfl

theorem cell23_1767204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_1767204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767204 prefixEnd_1767204 := by exact prefixLift 1767204
  have htrace : WordTrace (prefixWord ++ tailWord_1767204) baseStart_1767204 baseEnd_1767204 := by
    simpa [prefixWord, tailWord_1767204, baseEnd_1767204] using wordTrace_append hprefix tailTrace_1767204
  have hstable : (prefixWord ++ tailWord_1767204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767204).length < 2 ^ (prefixWord ++ tailWord_1767204).sum := by decide
  have hdescent : baseEnd_1767204 < baseStart_1767204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767238 : List Nat := [6, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_1767238 : Nat := 118140960795 + 1767238 * 2 ^ 59
def prefixEnd_1767238 : Nat := 4983230072969 + 3 ^ 40 * 1767238 * 2
def baseEnd_1767238 : Nat := 907442524890461906897627

theorem tailTrace_1767238 : CollatzResearch.WordTrace tailWord_1767238 prefixEnd_1767238 907442524890461906897627 := by
  unfold tailWord_1767238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2014264536612688158324199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42970976781070680710916245 2014264536612688158324199)
  ·
    refine ⟨3021396804919032237486299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2014264536612688158324199 3021396804919032237486299)
    ·
      refine ⟨4532095207378548356229449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3021396804919032237486299 4532095207378548356229449)
      ·
        refine ⟨3399071405533911267172087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4532095207378548356229449 3399071405533911267172087)
        ·
          refine ⟨5098607108300866900758131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3399071405533911267172087 5098607108300866900758131)
          ·
            refine ⟨7647910662451300351137197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5098607108300866900758131 7647910662451300351137197)
            ·
              refine ⟨2867966498419237631676449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7647910662451300351137197 2867966498419237631676449)
              ·
                refine ⟨2150974873814428223757337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2867966498419237631676449 2150974873814428223757337)
                ·
                  refine ⟨1613231155360821167818003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2150974873814428223757337 1613231155360821167818003)
                  ·
                    refine ⟨2419846733041231751727005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1613231155360821167818003 2419846733041231751727005)
                    ·
                      refine ⟨907442524890461906897627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2419846733041231751727005 907442524890461906897627)
                      ·
                        rfl

theorem cell23_1767238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_1767238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767238 prefixEnd_1767238 := by exact prefixLift 1767238
  have htrace : WordTrace (prefixWord ++ tailWord_1767238) baseStart_1767238 baseEnd_1767238 := by
    simpa [prefixWord, tailWord_1767238, baseEnd_1767238] using wordTrace_append hprefix tailTrace_1767238
  have hstable : (prefixWord ++ tailWord_1767238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767238).length < 2 ^ (prefixWord ++ tailWord_1767238).sum := by decide
  have hdescent : baseEnd_1767238 < baseStart_1767238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767240 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_1767240 : Nat := 118140960795 + 1767240 * 2 ^ 59
def prefixEnd_1767240 : Nat := 4983230072969 + 3 ^ 40 * 1767240 * 2
def baseEnd_1767240 : Nat := 907443551851770899072617

theorem tailTrace_1767240 : CollatzResearch.WordTrace tailWord_1767240 prefixEnd_1767240 907443551851770899072617 := by
  unfold tailWord_1767240
  simp only [CollatzResearch.WordTrace]
  refine ⟨32228269058799387703973587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42971025411732516938631449 32228269058799387703973587)
  ·
    refine ⟨48342403588199081555960381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32228269058799387703973587 48342403588199081555960381)
    ·
      refine ⟨18128401345574655583485143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48342403588199081555960381 18128401345574655583485143)
      ·
        refine ⟨27192602018361983375227715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18128401345574655583485143 27192602018361983375227715)
        ·
          refine ⟨40788903027542975062841573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27192602018361983375227715 40788903027542975062841573)
          ·
            refine ⟨7647919317664307824282795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40788903027542975062841573 7647919317664307824282795)
            ·
              refine ⟨11471878976496461736424193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7647919317664307824282795 11471878976496461736424193)
              ·
                refine ⟨8603909232372346302318145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11471878976496461736424193 8603909232372346302318145)
                ·
                  refine ⟨6452931924279259726738609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8603909232372346302318145 6452931924279259726738609)
                  ·
                    refine ⟨4839698943209444795053957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6452931924279259726738609 4839698943209444795053957)
                    ·
                      refine ⟨907443551851770899072617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4839698943209444795053957 907443551851770899072617)
                      ·
                        rfl

theorem cell23_1767240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_1767240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767240 prefixEnd_1767240 := by exact prefixLift 1767240
  have htrace : WordTrace (prefixWord ++ tailWord_1767240) baseStart_1767240 baseEnd_1767240 := by
    simpa [prefixWord, tailWord_1767240, baseEnd_1767240] using wordTrace_append hprefix tailTrace_1767240
  have hstable : (prefixWord ++ tailWord_1767240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767240).length < 2 ^ (prefixWord ++ tailWord_1767240).sum := by decide
  have hdescent : baseEnd_1767240 < baseStart_1767240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767250 : List Nat := [3, 2, 2, 1, 1, 3, 1, 3, 7]
def baseStart_1767250 : Nat := 118140960795 + 1767250 * 2 ^ 59
def prefixEnd_1767250 : Nat := 4983230072969 + 3 ^ 40 * 1767250 * 2
def baseEnd_1767250 : Nat := 100827631850923984438619

theorem tailTrace_1767250 : CollatzResearch.WordTrace tailWord_1767250 prefixEnd_1767250 100827631850923984438619 := by
  unfold tailWord_1767250
  simp only [CollatzResearch.WordTrace]
  refine ⟨16114225711890636778952801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42971268565041698077207469 16114225711890636778952801)
  ·
    refine ⟨12085669283917977584214601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16114225711890636778952801 12085669283917977584214601)
    ·
      refine ⟨9064251962938483188160951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12085669283917977584214601 9064251962938483188160951)
      ·
        refine ⟨13596377944407724782241427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9064251962938483188160951 13596377944407724782241427)
        ·
          refine ⟨20394566916611587173362141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13596377944407724782241427 20394566916611587173362141)
          ·
            refine ⟨7647962593729345190010803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20394566916611587173362141 7647962593729345190010803)
            ·
              refine ⟨11471943890594017785016205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7647962593729345190010803 11471943890594017785016205)
              ·
                refine ⟨4301978958972756669381077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11471943890594017785016205 4301978958972756669381077)
                ·
                  refine ⟨100827631850923984438619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4301978958972756669381077 100827631850923984438619)
                  ·
                    rfl

theorem cell23_1767250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_1767250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767250 prefixEnd_1767250 := by exact prefixLift 1767250
  have htrace : WordTrace (prefixWord ++ tailWord_1767250) baseStart_1767250 baseEnd_1767250 := by
    simpa [prefixWord, tailWord_1767250, baseEnd_1767250] using wordTrace_append hprefix tailTrace_1767250
  have hstable : (prefixWord ++ tailWord_1767250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767250).length < 2 ^ (prefixWord ++ tailWord_1767250).sum := by decide
  have hdescent : baseEnd_1767250 < baseStart_1767250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767280 : List Nat := [2, 1, 1, 1, 4, 1, 1, 5, 2, 5]
def baseStart_1767280 : Nat := 118140960795 + 1767280 * 2 ^ 59
def prefixEnd_1767280 : Nat := 4983230072969 + 3 ^ 40 * 1767280 * 2
def baseEnd_1767280 : Nat := 302488030359316914190811

theorem tailTrace_1767280 : CollatzResearch.WordTrace tailWord_1767280 prefixEnd_1767280 302488030359316914190811 := by
  unfold tailWord_1767280
  simp only [CollatzResearch.WordTrace]
  refine ⟨32228998518726931119701647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42971998024969241492935529 32228998518726931119701647)
  ·
    refine ⟨48343497778090396679552471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32228998518726931119701647 48343497778090396679552471)
    ·
      refine ⟨72515246667135595019328707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48343497778090396679552471 72515246667135595019328707)
      ·
        refine ⟨108772870000703392528993061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72515246667135595019328707 108772870000703392528993061)
        ·
          refine ⟨20394913125131886099186199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108772870000703392528993061 20394913125131886099186199)
          ·
            refine ⟨30592369687697829148779299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20394913125131886099186199 30592369687697829148779299)
            ·
              refine ⟨45888554531546743723168949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30592369687697829148779299 45888554531546743723168949)
              ·
                refine ⟨4302051987332507224047089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45888554531546743723168949 4302051987332507224047089)
                ·
                  refine ⟨3226538990499380418035317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4302051987332507224047089 3226538990499380418035317)
                  ·
                    refine ⟨302488030359316914190811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3226538990499380418035317 302488030359316914190811)
                    ·
                      rfl

theorem cell23_1767280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 2, 5].length) (baseStart_1767280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767280 prefixEnd_1767280 := by exact prefixLift 1767280
  have htrace : WordTrace (prefixWord ++ tailWord_1767280) baseStart_1767280 baseEnd_1767280 := by
    simpa [prefixWord, tailWord_1767280, baseEnd_1767280] using wordTrace_append hprefix tailTrace_1767280
  have hstable : (prefixWord ++ tailWord_1767280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767280).length < 2 ^ (prefixWord ++ tailWord_1767280).sum := by decide
  have hdescent : baseEnd_1767280 < baseStart_1767280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767317 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 1, 6, 2]
def baseStart_1767317 : Nat := 118140960795 + 1767317 * 2 ^ 59
def prefixEnd_1767317 : Nat := 4983230072969 + 3 ^ 40 * 1767317 * 2
def baseEnd_1767317 : Nat := 907483089862167097809763

theorem tailTrace_1767317 : CollatzResearch.WordTrace tailWord_1767317 prefixEnd_1767317 907483089862167097809763 := by
  unfold tailWord_1767317
  simp only [CollatzResearch.WordTrace]
  refine ⟨64459346538319817558500205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42972897692213211705666803 64459346538319817558500205)
  ·
    refine ⟨24172254951869931584437577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64459346538319817558500205 24172254951869931584437577)
    ·
      refine ⟨18129191213902448688328183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24172254951869931584437577 18129191213902448688328183)
      ·
        refine ⟨27193786820853673032492275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18129191213902448688328183 27193786820853673032492275)
        ·
          refine ⟨40790680231280509548738413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27193786820853673032492275 40790680231280509548738413)
          ·
            refine ⟨15296505086730191080776905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40790680231280509548738413 15296505086730191080776905)
            ·
              refine ⟨11472378815047643310582679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15296505086730191080776905 11472378815047643310582679)
              ·
                refine ⟨17208568222571464965874019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11472378815047643310582679 17208568222571464965874019)
                ·
                  refine ⟨25812852333857197448811029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17208568222571464965874019 25812852333857197448811029)
                  ·
                    refine ⟨1209977453149556130413017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25812852333857197448811029 1209977453149556130413017)
                    ·
                      refine ⟨907483089862167097809763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1209977453149556130413017 907483089862167097809763)
                      ·
                        rfl

theorem cell23_1767317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_1767317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767317 prefixEnd_1767317 := by exact prefixLift 1767317
  have htrace : WordTrace (prefixWord ++ tailWord_1767317) baseStart_1767317 baseEnd_1767317 := by
    simpa [prefixWord, tailWord_1767317, baseEnd_1767317] using wordTrace_append hprefix tailTrace_1767317
  have hstable : (prefixWord ++ tailWord_1767317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767317).length < 2 ^ (prefixWord ++ tailWord_1767317).sum := by decide
  have hdescent : baseEnd_1767317 < baseStart_1767317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767357 : List Nat := [1, 4, 1, 2, 3, 1, 1, 4, 6]
def baseStart_1767357 : Nat := 118140960795 + 1767357 * 2 ^ 59
def prefixEnd_1767357 : Nat := 4983230072969 + 3 ^ 40 * 1767357 * 2
def baseEnd_1767357 : Nat := 100833736565371882367731

theorem tailTrace_1767357 : CollatzResearch.WordTrace tailWord_1767357 prefixEnd_1767357 100833736565371882367731 := by
  unfold tailWord_1767357
  simp only [CollatzResearch.WordTrace]
  refine ⟨64460805458174904389956325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42973870305449936259970883 64460805458174904389956325)
  ·
    refine ⟨12086401023407794573116811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64460805458174904389956325 12086401023407794573116811)
    ·
      refine ⟨18129601535111691859675217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12086401023407794573116811 18129601535111691859675217)
      ·
        refine ⟨13597201151333768894756413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18129601535111691859675217 13597201151333768894756413)
        ·
          refine ⟨5098950431750163335533655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13597201151333768894756413 5098950431750163335533655)
          ·
            refine ⟨7648425647625245003300483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5098950431750163335533655 7648425647625245003300483)
            ·
              refine ⟨11472638471437867504950725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7648425647625245003300483 11472638471437867504950725)
              ·
                refine ⟨2151119713394600157178261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11472638471437867504950725 2151119713394600157178261)
                ·
                  refine ⟨100833736565371882367731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2151119713394600157178261 100833736565371882367731)
                  ·
                    rfl

theorem cell23_1767357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_1767357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767357 prefixEnd_1767357 := by exact prefixLift 1767357
  have htrace : WordTrace (prefixWord ++ tailWord_1767357) baseStart_1767357 baseEnd_1767357 := by
    simpa [prefixWord, tailWord_1767357, baseEnd_1767357] using wordTrace_append hprefix tailTrace_1767357
  have hstable : (prefixWord ++ tailWord_1767357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767357).length < 2 ^ (prefixWord ++ tailWord_1767357).sum := by decide
  have hdescent : baseEnd_1767357 < baseStart_1767357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767360 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 6]
def baseStart_1767360 : Nat := 118140960795 + 1767360 * 2 ^ 59
def prefixEnd_1767360 : Nat := 4983230072969 + 3 ^ 40 * 1767360 * 2
def baseEnd_1767360 : Nat := 907505169530310429572065

theorem tailTrace_1767360 : CollatzResearch.WordTrace tailWord_1767360 prefixEnd_1767360 907505169530310429572065 := by
  unfold tailWord_1767360
  simp only [CollatzResearch.WordTrace]
  refine ⟨32230457438582017951157767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42973943251442690601543689 32230457438582017951157767)
  ·
    refine ⟨48345686157873026926736651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32230457438582017951157767 48345686157873026926736651)
    ·
      refine ⟨72518529236809540390104977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48345686157873026926736651 72518529236809540390104977)
      ·
        refine ⟨54388896927607155292578733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72518529236809540390104977 54388896927607155292578733)
        ·
          refine ⟨20395836347852683234717025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54388896927607155292578733 20395836347852683234717025)
          ·
            refine ⟨15296877260889512426037769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20395836347852683234717025 15296877260889512426037769)
            ·
              refine ⟨11472657945667134319528327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15296877260889512426037769 11472657945667134319528327)
              ·
                refine ⟨17208986918500701479292491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11472657945667134319528327 17208986918500701479292491)
                ·
                  refine ⟨25813480377751052218938737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17208986918500701479292491 25813480377751052218938737)
                  ·
                    refine ⟨19360110283313289164204053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25813480377751052218938737 19360110283313289164204053)
                    ·
                      refine ⟨907505169530310429572065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19360110283313289164204053 907505169530310429572065)
                      ·
                        rfl

theorem cell23_1767360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_1767360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767360 prefixEnd_1767360 := by exact prefixLift 1767360
  have htrace : WordTrace (prefixWord ++ tailWord_1767360) baseStart_1767360 baseEnd_1767360 := by
    simpa [prefixWord, tailWord_1767360, baseEnd_1767360] using wordTrace_append hprefix tailTrace_1767360
  have hstable : (prefixWord ++ tailWord_1767360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767360).length < 2 ^ (prefixWord ++ tailWord_1767360).sum := by decide
  have hdescent : baseEnd_1767360 < baseStart_1767360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767384 : List Nat := [2, 1, 2, 2, 2, 2, 3, 2, 3, 1, 3]
def baseStart_1767384 : Nat := 118140960795 + 1767384 * 2 ^ 59
def prefixEnd_1767384 : Nat := 4983230072969 + 3 ^ 40 * 1767384 * 2
def baseEnd_1767384 : Nat := 907517493066018335671955

theorem tailTrace_1767384 : CollatzResearch.WordTrace tailWord_1767384 prefixEnd_1767384 907517493066018335671955 := by
  unfold tailWord_1767384
  simp only [CollatzResearch.WordTrace]
  refine ⟨32230895114538544000594603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42974526819384725334126137 32230895114538544000594603)
  ·
    refine ⟨48346342671807816000891905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32230895114538544000594603 48346342671807816000891905)
    ·
      refine ⟨36259757003855862000668929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48346342671807816000891905 36259757003855862000668929)
      ·
        refine ⟨27194817752891896500501697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36259757003855862000668929 27194817752891896500501697)
        ·
          refine ⟨20396113314668922375376273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27194817752891896500501697 20396113314668922375376273)
          ·
            refine ⟨15297084986001691781532205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20396113314668922375376273 15297084986001691781532205)
            ·
              refine ⟨5736406869750634418074577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15297084986001691781532205 5736406869750634418074577)
              ·
                refine ⟨4302305152312975813555933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5736406869750634418074577 4302305152312975813555933)
                ·
                  refine ⟨1613364432117365930083475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4302305152312975813555933 1613364432117365930083475)
                  ·
                    refine ⟨2420046648176048895125213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1613364432117365930083475 2420046648176048895125213)
                    ·
                      refine ⟨907517493066018335671955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2420046648176048895125213 907517493066018335671955)
                      ·
                        rfl

theorem cell23_1767384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_1767384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767384 prefixEnd_1767384 := by exact prefixLift 1767384
  have htrace : WordTrace (prefixWord ++ tailWord_1767384) baseStart_1767384 baseEnd_1767384 := by
    simpa [prefixWord, tailWord_1767384, baseEnd_1767384] using wordTrace_append hprefix tailTrace_1767384
  have hstable : (prefixWord ++ tailWord_1767384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767384).length < 2 ^ (prefixWord ++ tailWord_1767384).sum := by decide
  have hdescent : baseEnd_1767384 < baseStart_1767384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767388 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_1767388 : Nat := 118140960795 + 1767388 * 2 ^ 59
def prefixEnd_1767388 : Nat := 4983230072969 + 3 ^ 40 * 1767388 * 2
def baseEnd_1767388 : Nat := 907519546988636320021937

theorem tailTrace_1767388 : CollatzResearch.WordTrace tailWord_1767388 prefixEnd_1767388 907519546988636320021937 := by
  unfold tailWord_1767388
  simp only [CollatzResearch.WordTrace]
  refine ⟨32230968060531298342167409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42974624080708397789556545 32230968060531298342167409)
  ·
    refine ⟨24173226045398473756625557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32230968060531298342167409 24173226045398473756625557)
    ·
      refine ⟨1133119970878053457341823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24173226045398473756625557 1133119970878053457341823)
      ·
        refine ⟨1699679956317080186012735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1133119970878053457341823 1699679956317080186012735)
        ·
          refine ⟨2549519934475620279019103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1699679956317080186012735 2549519934475620279019103)
          ·
            refine ⟨3824279901713430418528655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549519934475620279019103 3824279901713430418528655)
            ·
              refine ⟨5736419852570145627792983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3824279901713430418528655 5736419852570145627792983)
              ·
                refine ⟨8604629778855218441689475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5736419852570145627792983 8604629778855218441689475)
                ·
                  refine ⟨12906944668282827662534213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8604629778855218441689475 12906944668282827662534213)
                  ·
                    refine ⟨2420052125303030186725165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12906944668282827662534213 2420052125303030186725165)
                    ·
                      refine ⟨907519546988636320021937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2420052125303030186725165 907519546988636320021937)
                      ·
                        rfl

theorem cell23_1767388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_1767388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767388 prefixEnd_1767388 := by exact prefixLift 1767388
  have htrace : WordTrace (prefixWord ++ tailWord_1767388) baseStart_1767388 baseEnd_1767388 := by
    simpa [prefixWord, tailWord_1767388, baseEnd_1767388] using wordTrace_append hprefix tailTrace_1767388
  have hstable : (prefixWord ++ tailWord_1767388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767388).length < 2 ^ (prefixWord ++ tailWord_1767388).sum := by decide
  have hdescent : baseEnd_1767388 < baseStart_1767388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767427 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 3]
def baseStart_1767427 : Nat := 118140960795 + 1767427 * 2 ^ 59
def prefixEnd_1767427 : Nat := 4983230072969 + 3 ^ 40 * 1767427 * 2
def baseEnd_1767427 : Nat := 907539572734161667434257

theorem tailTrace_1767427 : CollatzResearch.WordTrace tailWord_1767427 prefixEnd_1767427 907539572734161667434257 := by
  unfold tailWord_1767427
  simp only [CollatzResearch.WordTrace]
  refine ⟨64463358567921306345004535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42975572378614204230003023 64463358567921306345004535)
  ·
    refine ⟨96695037851881959517506803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64463358567921306345004535 96695037851881959517506803)
    ·
      refine ⟨145042556777822939276260205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96695037851881959517506803 145042556777822939276260205)
      ·
        refine ⟨54390958791683602228597577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145042556777822939276260205 54390958791683602228597577)
        ·
          refine ⟨40793219093762701671448183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54390958791683602228597577 40793219093762701671448183)
          ·
            refine ⟨61189828640644052507172275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40793219093762701671448183 61189828640644052507172275)
            ·
              refine ⟨91784742960966078760758413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61189828640644052507172275 91784742960966078760758413)
              ·
                refine ⟨34419278610362279535284405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91784742960966078760758413 34419278610362279535284405)
                ·
                  refine ⟨3226807369721463706432913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34419278610362279535284405 3226807369721463706432913)
                  ·
                    refine ⟨2420105527291097779824685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3226807369721463706432913 2420105527291097779824685)
                    ·
                      refine ⟨907539572734161667434257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2420105527291097779824685 907539572734161667434257)
                      ·
                        rfl

theorem cell23_1767427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_1767427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767427 prefixEnd_1767427 := by exact prefixLift 1767427
  have htrace : WordTrace (prefixWord ++ tailWord_1767427) baseStart_1767427 baseEnd_1767427 := by
    simpa [prefixWord, tailWord_1767427, baseEnd_1767427] using wordTrace_append hprefix tailTrace_1767427
  have hstable : (prefixWord ++ tailWord_1767427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767427).length < 2 ^ (prefixWord ++ tailWord_1767427).sum := by decide
  have hdescent : baseEnd_1767427 < baseStart_1767427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767440 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 7]
def baseStart_1767440 : Nat := 118140960795 + 1767440 * 2 ^ 59
def prefixEnd_1767440 : Nat := 4983230072969 + 3 ^ 40 * 1767440 * 2
def baseEnd_1767440 : Nat := 907546247982670116571697

theorem tailTrace_1767440 : CollatzResearch.WordTrace tailWord_1767440 prefixEnd_1767440 907546247982670116571697 := by
  unfold tailWord_1767440
  simp only [CollatzResearch.WordTrace]
  refine ⟨32231916358437104782613887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42975888477916139710151849 32231916358437104782613887)
  ·
    refine ⟨48347874537655657173920831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32231916358437104782613887 48347874537655657173920831)
    ·
      refine ⟨72521811806483485760881247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48347874537655657173920831 72521811806483485760881247)
      ·
        refine ⟨108782717709725228641321871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72521811806483485760881247 108782717709725228641321871)
        ·
          refine ⟨163174076564587842961982807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108782717709725228641321871 163174076564587842961982807)
          ·
            refine ⟨244761114846881764442974211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163174076564587842961982807 244761114846881764442974211)
            ·
              refine ⟨367141672270322646664461317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244761114846881764442974211 367141672270322646664461317)
              ·
                refine ⟨68839063550685496249586497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 367141672270322646664461317 68839063550685496249586497)
                ·
                  refine ⟨51629297663014122187189873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68839063550685496249586497 51629297663014122187189873)
                  ·
                    refine ⟨38721973247260591640392405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51629297663014122187189873 38721973247260591640392405)
                    ·
                      refine ⟨907546247982670116571697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38721973247260591640392405 907546247982670116571697)
                      ·
                        rfl

theorem cell23_1767440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_1767440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767440 prefixEnd_1767440 := by exact prefixLift 1767440
  have htrace : WordTrace (prefixWord ++ tailWord_1767440) baseStart_1767440 baseEnd_1767440 := by
    simpa [prefixWord, tailWord_1767440, baseEnd_1767440] using wordTrace_append hprefix tailTrace_1767440
  have hstable : (prefixWord ++ tailWord_1767440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767440).length < 2 ^ (prefixWord ++ tailWord_1767440).sum := by decide
  have hdescent : baseEnd_1767440 < baseStart_1767440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767534 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_1767534 : Nat := 118140960795 + 1767534 * 2 ^ 59
def prefixEnd_1767534 : Nat := 4983230072969 + 3 ^ 40 * 1767534 * 2
def baseEnd_1767534 : Nat := 907594515164192748796265

theorem tailTrace_1767534 : CollatzResearch.WordTrace tailWord_1767534 prefixEnd_1767534 907594515164192748796265 := by
  unfold tailWord_1767534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8058407647316707952393707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42978174119022442412766437 8058407647316707952393707)
  ·
    refine ⟨12087611470975061928590561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8058407647316707952393707 12087611470975061928590561)
    ·
      refine ⟨9065708603231296446442921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12087611470975061928590561 9065708603231296446442921)
      ·
        refine ⟨6799281452423472334832191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9065708603231296446442921 6799281452423472334832191)
        ·
          refine ⟨10198922178635208502248287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6799281452423472334832191 10198922178635208502248287)
          ·
            refine ⟨15298383267952812753372431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10198922178635208502248287 15298383267952812753372431)
            ·
              refine ⟨22947574901929219130058647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15298383267952812753372431 22947574901929219130058647)
              ·
                refine ⟨34421362352893828695087971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22947574901929219130058647 34421362352893828695087971)
                ·
                  refine ⟨51632043529340743042631957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34421362352893828695087971 51632043529340743042631957)
                  ·
                    refine ⟨2420252040437847330123373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51632043529340743042631957 2420252040437847330123373)
                    ·
                      refine ⟨907594515164192748796265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2420252040437847330123373 907594515164192748796265)
                      ·
                        rfl

theorem cell23_1767534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_1767534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767534 prefixEnd_1767534 := by exact prefixLift 1767534
  have htrace : WordTrace (prefixWord ++ tailWord_1767534) baseStart_1767534 baseEnd_1767534 := by
    simpa [prefixWord, tailWord_1767534, baseEnd_1767534] using wordTrace_append hprefix tailTrace_1767534
  have hstable : (prefixWord ++ tailWord_1767534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767534).length < 2 ^ (prefixWord ++ tailWord_1767534).sum := by decide
  have hdescent : baseEnd_1767534 < baseStart_1767534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767537 : List Nat := [1, 2, 2, 2, 1, 1, 4, 3, 7]
def baseStart_1767537 : Nat := 118140960795 + 1767537 * 2 ^ 59
def prefixEnd_1767537 : Nat := 4983230072969 + 3 ^ 40 * 1767537 * 2
def baseEnd_1767537 : Nat := 100844006178461804117639

theorem tailTrace_1767537 : CollatzResearch.WordTrace tailWord_1767537 prefixEnd_1767537 100844006178461804117639 := by
  unfold tailWord_1767537
  simp only [CollatzResearch.WordTrace]
  refine ⟨64467370597522795131508865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42978247065015196754339243 64467370597522795131508865)
  ·
    refine ⟨48350527948142096348631649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64467370597522795131508865 48350527948142096348631649)
    ·
      refine ⟨36262895961106572261473737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48350527948142096348631649 36262895961106572261473737)
      ·
        refine ⟨27197171970829929196105303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36262895961106572261473737 27197171970829929196105303)
        ·
          refine ⟨40795757956244893794157955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27197171970829929196105303 40795757956244893794157955)
          ·
            refine ⟨61193636934367340691236933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40795757956244893794157955 61193636934367340691236933)
            ·
              refine ⟨11473806925193876379606925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61193636934367340691236933 11473806925193876379606925)
              ·
                refine ⟨4302677596947703642352597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11473806925193876379606925 4302677596947703642352597)
                ·
                  refine ⟨100844006178461804117639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4302677596947703642352597 100844006178461804117639)
                  ·
                    rfl

theorem cell23_1767537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 7].length) (baseStart_1767537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767537 prefixEnd_1767537 := by exact prefixLift 1767537
  have htrace : WordTrace (prefixWord ++ tailWord_1767537) baseStart_1767537 baseEnd_1767537 := by
    simpa [prefixWord, tailWord_1767537, baseEnd_1767537] using wordTrace_append hprefix tailTrace_1767537
  have hstable : (prefixWord ++ tailWord_1767537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767537).length < 2 ^ (prefixWord ++ tailWord_1767537).sum := by decide
  have hdescent : baseEnd_1767537 < baseStart_1767537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767548 : List Nat := [2, 2, 2, 1, 1, 4, 2, 3, 2, 2, 2]
def baseStart_1767548 : Nat := 118140960795 + 1767548 * 2 ^ 59
def prefixEnd_1767548 : Nat := 4983230072969 + 3 ^ 40 * 1767548 * 2
def baseEnd_1767548 : Nat := 907601703893355694021201

theorem tailTrace_1767548 : CollatzResearch.WordTrace tailWord_1767548 prefixEnd_1767548 907601703893355694021201 := by
  unfold tailWord_1767548
  simp only [CollatzResearch.WordTrace]
  refine ⟨32233885900241472005079649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42978514533655296006772865 32233885900241472005079649)
  ·
    refine ⟨24175414425181104003809737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32233885900241472005079649 24175414425181104003809737)
    ·
      refine ⟨18131560818885828002857303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24175414425181104003809737 18131560818885828002857303)
      ·
        refine ⟨27197341228328742004285955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18131560818885828002857303 27197341228328742004285955)
        ·
          refine ⟨40796011842493113006428933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27197341228328742004285955 40796011842493113006428933)
          ·
            refine ⟨7649252220467458688705425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40796011842493113006428933 7649252220467458688705425)
            ·
              refine ⟨5736939165350594016529069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7649252220467458688705425 5736939165350594016529069)
              ·
                refine ⟨2151352187006472756198401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5736939165350594016529069 2151352187006472756198401)
                ·
                  refine ⟨1613514140254854567148801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2151352187006472756198401 1613514140254854567148801)
                  ·
                    refine ⟨1210135605191140925361601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1613514140254854567148801 1210135605191140925361601)
                    ·
                      refine ⟨907601703893355694021201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1210135605191140925361601 907601703893355694021201)
                      ·
                        rfl

theorem cell23_1767548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_1767548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767548 prefixEnd_1767548 := by exact prefixLift 1767548
  have htrace : WordTrace (prefixWord ++ tailWord_1767548) baseStart_1767548 baseEnd_1767548 := by
    simpa [prefixWord, tailWord_1767548, baseEnd_1767548] using wordTrace_append hprefix tailTrace_1767548
  have hstable : (prefixWord ++ tailWord_1767548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767548).length < 2 ^ (prefixWord ++ tailWord_1767548).sum := by decide
  have hdescent : baseEnd_1767548 < baseStart_1767548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767577 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 3, 2, 5]
def baseStart_1767577 : Nat := 118140960795 + 1767577 * 2 ^ 59
def prefixEnd_1767577 : Nat := 4983230072969 + 3 ^ 40 * 1767577 * 2
def baseEnd_1767577 : Nat := 907616594832336080558567

theorem tailTrace_1767577 : CollatzResearch.WordTrace tailWord_1767577 prefixEnd_1767577 907616594832336080558567 := by
  unfold tailWord_1767577
  simp only [CollatzResearch.WordTrace]
  refine ⟨64468829517377881962964985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42979219678251921308643323 64468829517377881962964985)
  ·
    refine ⟨48351622138033411472223739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64468829517377881962964985 48351622138033411472223739)
    ·
      refine ⟨72527433207050117208335609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48351622138033411472223739 72527433207050117208335609)
      ·
        refine ⟨54395574905287587906251707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72527433207050117208335609 54395574905287587906251707)
        ·
          refine ⟨81593362357931381859377561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54395574905287587906251707 81593362357931381859377561)
          ·
            refine ⟨61195021768448536394533171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81593362357931381859377561 61195021768448536394533171)
            ·
              refine ⟨91792532652672804591799757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61195021768448536394533171 91792532652672804591799757)
              ·
                refine ⟨34422199744752301721924909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91792532652672804591799757 34422199744752301721924909)
                ·
                  refine ⟨12908324904282113145721841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34422199744752301721924909 12908324904282113145721841)
                  ·
                    refine ⟨9681243678211584859291381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12908324904282113145721841 9681243678211584859291381)
                    ·
                      refine ⟨907616594832336080558567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9681243678211584859291381 907616594832336080558567)
                      ·
                        rfl

theorem cell23_1767577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_1767577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767577 prefixEnd_1767577 := by exact prefixLift 1767577
  have htrace : WordTrace (prefixWord ++ tailWord_1767577) baseStart_1767577 baseEnd_1767577 := by
    simpa [prefixWord, tailWord_1767577, baseEnd_1767577] using wordTrace_append hprefix tailTrace_1767577
  have hstable : (prefixWord ++ tailWord_1767577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767577).length < 2 ^ (prefixWord ++ tailWord_1767577).sum := by decide
  have hdescent : baseEnd_1767577 < baseStart_1767577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767618 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_1767618 : Nat := 118140960795 + 1767618 * 2 ^ 59
def prefixEnd_1767618 : Nat := 4983230072969 + 3 ^ 40 * 1767618 * 2
def baseEnd_1767618 : Nat := 302545882513056806715293

theorem tailTrace_1767618 : CollatzResearch.WordTrace tailWord_1767618 prefixEnd_1767618 302545882513056806715293 := by
  unfold tailWord_1767618
  simp only [CollatzResearch.WordTrace]
  refine ⟨16117581227557336491301877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42980216606819563976805005 16117581227557336491301877)
  ·
    refine ⟨1511023240083500296059551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16117581227557336491301877 1511023240083500296059551)
    ·
      refine ⟨2266534860125250444089327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1511023240083500296059551 2266534860125250444089327)
      ·
        refine ⟨3399802290187875666133991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2266534860125250444089327 3399802290187875666133991)
        ·
          refine ⟨5099703435281813499200987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3399802290187875666133991 5099703435281813499200987)
          ·
            refine ⟨7649555152922720248801481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5099703435281813499200987 7649555152922720248801481)
            ·
              refine ⟨5737166364692040186601111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7649555152922720248801481 5737166364692040186601111)
              ·
                refine ⟨8605749547038060279901667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5737166364692040186601111 8605749547038060279901667)
                ·
                  refine ⟨12908624320557090419852501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8605749547038060279901667 12908624320557090419852501)
                  ·
                    refine ⟨302545882513056806715293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12908624320557090419852501 302545882513056806715293)
                    ·
                      rfl

theorem cell23_1767618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_1767618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767618 prefixEnd_1767618 := by exact prefixLift 1767618
  have htrace : WordTrace (prefixWord ++ tailWord_1767618) baseStart_1767618 baseEnd_1767618 := by
    simpa [prefixWord, tailWord_1767618, baseEnd_1767618] using wordTrace_append hprefix tailTrace_1767618
  have hstable : (prefixWord ++ tailWord_1767618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767618).length < 2 ^ (prefixWord ++ tailWord_1767618).sum := by decide
  have hdescent : baseEnd_1767618 < baseStart_1767618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767627 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 10]
def baseStart_1767627 : Nat := 118140960795 + 1767627 * 2 ^ 59
def prefixEnd_1767627 : Nat := 4983230072969 + 3 ^ 40 * 1767627 * 2
def baseEnd_1767627 : Nat := 100849140985006764992593

theorem tailTrace_1767627 : CollatzResearch.WordTrace tailWord_1767627 prefixEnd_1767627 100849140985006764992593 := by
  unfold tailWord_1767627
  simp only [CollatzResearch.WordTrace]
  refine ⟨64470653167196740502285135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42980435444797827001523423 64470653167196740502285135)
  ·
    refine ⟨96705979750795110753427703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64470653167196740502285135 96705979750795110753427703)
    ·
      refine ⟨145058969626192666130141555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96705979750795110753427703 145058969626192666130141555)
      ·
        refine ⟨217588454439288999195212333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145058969626192666130141555 217588454439288999195212333)
        ·
          refine ⟨81595670414733374698204625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217588454439288999195212333 81595670414733374698204625)
          ·
            refine ⟨61196752811050031023653469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81595670414733374698204625 61196752811050031023653469)
            ·
              refine ⟨22948782304143761633870051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61196752811050031023653469 22948782304143761633870051)
              ·
                refine ⟨34423173456215642450805077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22948782304143761633870051 34423173456215642450805077)
                ·
                  refine ⟨100849140985006764992593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 34423173456215642450805077 100849140985006764992593)
                  ·
                    rfl

theorem cell23_1767627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 10].length) (baseStart_1767627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767627 prefixEnd_1767627 := by exact prefixLift 1767627
  have htrace : WordTrace (prefixWord ++ tailWord_1767627) baseStart_1767627 baseEnd_1767627 := by
    simpa [prefixWord, tailWord_1767627, baseEnd_1767627] using wordTrace_append hprefix tailTrace_1767627
  have hstable : (prefixWord ++ tailWord_1767627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767627).length < 2 ^ (prefixWord ++ tailWord_1767627).sum := by decide
  have hdescent : baseEnd_1767627 < baseStart_1767627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767638 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1767638 : Nat := 118140960795 + 1767638 * 2 ^ 59
def prefixEnd_1767638 : Nat := 4983230072969 + 3 ^ 40 * 1767638 * 2
def baseEnd_1767638 : Nat := 907647917152260341895787

theorem tailTrace_1767638 : CollatzResearch.WordTrace tailWord_1767638 prefixEnd_1767638 907647917152260341895787 := by
  unfold tailWord_1767638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4029440898134805586308473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42980702913437926253957045 4029440898134805586308473)
  ·
    refine ⟨3022080673601104189731355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4029440898134805586308473 3022080673601104189731355)
    ·
      refine ⟨4533121010401656284597033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3022080673601104189731355 4533121010401656284597033)
      ·
        refine ⟨3399840757801242213447775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4533121010401656284597033 3399840757801242213447775)
        ·
          refine ⟨5099761136701863320171663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3399840757801242213447775 5099761136701863320171663)
          ·
            refine ⟨7649641705052794980257495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5099761136701863320171663 7649641705052794980257495)
            ·
              refine ⟨11474462557579192470386243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7649641705052794980257495 11474462557579192470386243)
              ·
                refine ⟨17211693836368788705579365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11474462557579192470386243 17211693836368788705579365)
                ·
                  refine ⟨3227192594319147882296131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17211693836368788705579365 3227192594319147882296131)
                  ·
                    refine ⟨4840788891478721823444197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3227192594319147882296131 4840788891478721823444197)
                    ·
                      refine ⟨907647917152260341895787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4840788891478721823444197 907647917152260341895787)
                      ·
                        rfl

theorem cell23_1767638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1767638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767638 prefixEnd_1767638 := by exact prefixLift 1767638
  have htrace : WordTrace (prefixWord ++ tailWord_1767638) baseStart_1767638 baseEnd_1767638 := by
    simpa [prefixWord, tailWord_1767638, baseEnd_1767638] using wordTrace_append hprefix tailTrace_1767638
  have hstable : (prefixWord ++ tailWord_1767638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767638).length < 2 ^ (prefixWord ++ tailWord_1767638).sum := by decide
  have hdescent : baseEnd_1767638 < baseStart_1767638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767704 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 3, 6]
def baseStart_1767704 : Nat := 118140960795 + 1767704 * 2 ^ 59
def prefixEnd_1767704 : Nat := 4983230072969 + 3 ^ 40 * 1767704 * 2
def baseEnd_1767704 : Nat := 302560602291819027890161

theorem tailTrace_1767704 : CollatzResearch.WordTrace tailWord_1767704 prefixEnd_1767704 302560602291819027890161 := by
  unfold tailWord_1767704
  simp only [CollatzResearch.WordTrace]
  refine ⟨32236730793958891326419083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42982307725278521768558777 32236730793958891326419083)
  ·
    refine ⟨48355096190938336989628625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32236730793958891326419083 48355096190938336989628625)
    ·
      refine ⟨36266322143203752742221469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48355096190938336989628625 36266322143203752742221469)
      ·
        refine ⟨13599870803701407278333051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36266322143203752742221469 13599870803701407278333051)
        ·
          refine ⟨20399806205552110917499577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13599870803701407278333051 20399806205552110917499577)
          ·
            refine ⟨15299854654164083188124683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20399806205552110917499577 15299854654164083188124683)
            ·
              refine ⟨22949781981246124782187025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15299854654164083188124683 22949781981246124782187025)
              ·
                refine ⟨17212336485934593586640269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22949781981246124782187025 17212336485934593586640269)
                ·
                  refine ⟨6454626182225472594990101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17212336485934593586640269 6454626182225472594990101)
                  ·
                    refine ⟨302560602291819027890161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6454626182225472594990101 302560602291819027890161)
                    ·
                      rfl

theorem cell23_1767704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_1767704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767704 prefixEnd_1767704 := by exact prefixLift 1767704
  have htrace : WordTrace (prefixWord ++ tailWord_1767704) baseStart_1767704 baseEnd_1767704 := by
    simpa [prefixWord, tailWord_1767704, baseEnd_1767704] using wordTrace_append hprefix tailTrace_1767704
  have hstable : (prefixWord ++ tailWord_1767704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767704).length < 2 ^ (prefixWord ++ tailWord_1767704).sum := by decide
  have hdescent : baseEnd_1767704 < baseStart_1767704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767711 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 4]
def baseStart_1767711 : Nat := 118140960795 + 1767711 * 2 ^ 59
def prefixEnd_1767711 : Nat := 4983230072969 + 3 ^ 40 * 1767711 * 2
def baseEnd_1767711 : Nat := 907685401240038556282951

theorem tailTrace_1767711 : CollatzResearch.WordTrace tailWord_1767711 prefixEnd_1767711 907685401240038556282951 := by
  unfold tailWord_1767711
  simp only [CollatzResearch.WordTrace]
  refine ⟨64473716898892422848342987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42982477932594948565561991 64473716898892422848342987)
  ·
    refine ⟨96710575348338634272514481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64473716898892422848342987 96710575348338634272514481)
    ·
      refine ⟨72532931511253975704385861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96710575348338634272514481 72532931511253975704385861)
      ·
        refine ⟨13599924658360120444572349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72532931511253975704385861 13599924658360120444572349)
        ·
          refine ⟨5099971746885045166714631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13599924658360120444572349 5099971746885045166714631)
          ·
            refine ⟨7649957620327567750071947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5099971746885045166714631 7649957620327567750071947)
            ·
              refine ⟨11474936430491351625107921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7649957620327567750071947 11474936430491351625107921)
              ·
                refine ⟨8606202322868513718830941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11474936430491351625107921 8606202322868513718830941)
                ·
                  refine ⟨3227325871075692644561603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8606202322868513718830941 3227325871075692644561603)
                  ·
                    refine ⟨4840988806613538966842405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3227325871075692644561603 4840988806613538966842405)
                    ·
                      refine ⟨907685401240038556282951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4840988806613538966842405 907685401240038556282951)
                      ·
                        rfl

theorem cell23_1767711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_1767711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767711 prefixEnd_1767711 := by exact prefixLift 1767711
  have htrace : WordTrace (prefixWord ++ tailWord_1767711) baseStart_1767711 baseEnd_1767711 := by
    simpa [prefixWord, tailWord_1767711, baseEnd_1767711] using wordTrace_append hprefix tailTrace_1767711
  have hstable : (prefixWord ++ tailWord_1767711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767711).length < 2 ^ (prefixWord ++ tailWord_1767711).sum := by decide
  have hdescent : baseEnd_1767711 < baseStart_1767711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767724 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 6]
def baseStart_1767724 : Nat := 118140960795 + 1767724 * 2 ^ 59
def prefixEnd_1767724 : Nat := 4983230072969 + 3 ^ 40 * 1767724 * 2
def baseEnd_1767724 : Nat := 907692076488547005420391

theorem tailTrace_1767724 : CollatzResearch.WordTrace tailWord_1767724 prefixEnd_1767724 907692076488547005420391 := by
  unfold tailWord_1767724
  simp only [CollatzResearch.WordTrace]
  refine ⟨32237095523922663034283113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42982794031896884045710817 32237095523922663034283113)
  ·
    refine ⟨24177821642941997275712335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32237095523922663034283113 24177821642941997275712335)
    ·
      refine ⟨36266732464412995913568503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24177821642941997275712335 36266732464412995913568503)
      ·
        refine ⟨54400098696619493870352755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36266732464412995913568503 54400098696619493870352755)
        ·
          refine ⟨81600148044929240805529133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54400098696619493870352755 81600148044929240805529133)
          ·
            refine ⟨30600055516848465302073425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81600148044929240805529133 30600055516848465302073425)
            ·
              refine ⟨22950041637636348976555069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30600055516848465302073425 22950041637636348976555069)
              ·
                refine ⟨8606265614113630866208151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22950041637636348976555069 8606265614113630866208151)
                ·
                  refine ⟨12909398421170446299312227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8606265614113630866208151 12909398421170446299312227)
                  ·
                    refine ⟨19364097631755669448968341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12909398421170446299312227 19364097631755669448968341)
                    ·
                      refine ⟨907692076488547005420391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19364097631755669448968341 907692076488547005420391)
                      ·
                        rfl

theorem cell23_1767724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_1767724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767724 prefixEnd_1767724 := by exact prefixLift 1767724
  have htrace : WordTrace (prefixWord ++ tailWord_1767724) baseStart_1767724 baseEnd_1767724 := by
    simpa [prefixWord, tailWord_1767724, baseEnd_1767724] using wordTrace_append hprefix tailTrace_1767724
  have hstable : (prefixWord ++ tailWord_1767724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767724).length < 2 ^ (prefixWord ++ tailWord_1767724).sum := by decide
  have hdescent : baseEnd_1767724 < baseStart_1767724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767731 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 3]
def baseStart_1767731 : Nat := 118140960795 + 1767731 * 2 ^ 59
def prefixEnd_1767731 : Nat := 4983230072969 + 3 ^ 40 * 1767731 * 2
def baseEnd_1767731 : Nat := 907695670853128478032859

theorem tailTrace_1767731 : CollatzResearch.WordTrace tailWord_1767731 prefixEnd_1767731 907695670853128478032859 := by
  unfold tailWord_1767731
  simp only [CollatzResearch.WordTrace]
  refine ⟨64474446358819966264071047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42982964239213310842714031 64474446358819966264071047)
  ·
    refine ⟨96711669538229949396106571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64474446358819966264071047 96711669538229949396106571)
    ·
      refine ⟨145067504307344924094159857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96711669538229949396106571 145067504307344924094159857)
      ·
        refine ⟨108800628230508693070619893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145067504307344924094159857 108800628230508693070619893)
        ·
          refine ⟨10200058896610189975370615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108800628230508693070619893 10200058896610189975370615)
          ·
            refine ⟨15300088344915284963055923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10200058896610189975370615 15300088344915284963055923)
            ·
              refine ⟨22950132517372927444583885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15300088344915284963055923 22950132517372927444583885)
              ·
                refine ⟨8606299694014847791718957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22950132517372927444583885 8606299694014847791718957)
                ·
                  refine ⟨3227362385255567921894609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8606299694014847791718957 3227362385255567921894609)
                  ·
                    refine ⟨2420521788941675941420957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3227362385255567921894609 2420521788941675941420957)
                    ·
                      refine ⟨907695670853128478032859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2420521788941675941420957 907695670853128478032859)
                      ·
                        rfl

theorem cell23_1767731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 3].length) (baseStart_1767731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767731 prefixEnd_1767731 := by exact prefixLift 1767731
  have htrace : WordTrace (prefixWord ++ tailWord_1767731) baseStart_1767731 baseEnd_1767731 := by
    simpa [prefixWord, tailWord_1767731, baseEnd_1767731] using wordTrace_append hprefix tailTrace_1767731
  have hstable : (prefixWord ++ tailWord_1767731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767731).length < 2 ^ (prefixWord ++ tailWord_1767731).sum := by decide
  have hdescent : baseEnd_1767731 < baseStart_1767731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767732 : List Nat := [2, 5, 1, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_1767732 : Nat := 118140960795 + 1767732 * 2 ^ 59
def prefixEnd_1767732 : Nat := 4983230072969 + 3 ^ 40 * 1767732 * 2
def baseEnd_1767732 : Nat := 907696184333782974120355

theorem tailTrace_1767732 : CollatzResearch.WordTrace tailWord_1767732 prefixEnd_1767732 907696184333782974120355 := by
  unfold tailWord_1767732
  simp only [CollatzResearch.WordTrace]
  refine ⟨32237241415908171717428725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42982988554544228956571633 32237241415908171717428725)
  ·
    refine ⟨3022241382741391098508943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32237241415908171717428725 3022241382741391098508943)
    ·
      refine ⟨4533362074112086647763415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3022241382741391098508943 4533362074112086647763415)
      ·
        refine ⟨6800043111168129971645123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4533362074112086647763415 6800043111168129971645123)
        ·
          refine ⟨10200064666752194957467685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6800043111168129971645123 10200064666752194957467685)
          ·
            refine ⟨1912512125016036554525191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10200064666752194957467685 1912512125016036554525191)
            ·
              refine ⟨2868768187524054831787787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1912512125016036554525191 2868768187524054831787787)
              ·
                refine ⟨4303152281286082247681681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2868768187524054831787787 4303152281286082247681681)
                ·
                  refine ⟨3227364210964561685761261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4303152281286082247681681 3227364210964561685761261)
                  ·
                    refine ⟨1210261579111710632160473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3227364210964561685761261 1210261579111710632160473)
                    ·
                      refine ⟨907696184333782974120355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1210261579111710632160473 907696184333782974120355)
                      ·
                        rfl

theorem cell23_1767732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_1767732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767732 prefixEnd_1767732 := by exact prefixLift 1767732
  have htrace : WordTrace (prefixWord ++ tailWord_1767732) baseStart_1767732 baseEnd_1767732 := by
    simpa [prefixWord, tailWord_1767732, baseEnd_1767732] using wordTrace_append hprefix tailTrace_1767732
  have hstable : (prefixWord ++ tailWord_1767732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767732).length < 2 ^ (prefixWord ++ tailWord_1767732).sum := by decide
  have hdescent : baseEnd_1767732 < baseStart_1767732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767745 : List Nat := [1, 2, 5, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_1767745 : Nat := 118140960795 + 1767745 * 2 ^ 59
def prefixEnd_1767745 : Nat := 4983230072969 + 3 ^ 40 * 1767745 * 2
def baseEnd_1767745 : Nat := 907702859582291423257795

theorem tailTrace_1767745 : CollatzResearch.WordTrace tailWord_1767745 prefixEnd_1767745 907702859582291423257795 := by
  unfold tailWord_1767745
  simp only [CollatzResearch.WordTrace]
  refine ⟨64474956980769246655080689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42983304653846164436720459 64474956980769246655080689)
  ·
    refine ⟨48356217735576934991310517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64474956980769246655080689 48356217735576934991310517)
    ·
      refine ⟨4533395412710337655435361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48356217735576934991310517 4533395412710337655435361)
      ·
        refine ⟨3400046559532753241576521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4533395412710337655435361 3400046559532753241576521)
        ·
          refine ⟨2550034919649564931182391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3400046559532753241576521 2550034919649564931182391)
          ·
            refine ⟨3825052379474347396773587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2550034919649564931182391 3825052379474347396773587)
            ·
              refine ⟨5737578569211521095160381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3825052379474347396773587 5737578569211521095160381)
              ·
                refine ⟨2151591963454320410685143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5737578569211521095160381 2151591963454320410685143)
                ·
                  refine ⟨3227387945181480616027715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151591963454320410685143 3227387945181480616027715)
                  ·
                    refine ⟨4841081917772220924041573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3227387945181480616027715 4841081917772220924041573)
                    ·
                      refine ⟨907702859582291423257795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4841081917772220924041573 907702859582291423257795)
                      ·
                        rfl

theorem cell23_1767745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_1767745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767745 prefixEnd_1767745 := by exact prefixLift 1767745
  have htrace : WordTrace (prefixWord ++ tailWord_1767745) baseStart_1767745 baseEnd_1767745 := by
    simpa [prefixWord, tailWord_1767745, baseEnd_1767745] using wordTrace_append hprefix tailTrace_1767745
  have hstable : (prefixWord ++ tailWord_1767745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767745).length < 2 ^ (prefixWord ++ tailWord_1767745).sum := by decide
  have hdescent : baseEnd_1767745 < baseStart_1767745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767754 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_1767754 : Nat := 118140960795 + 1767754 * 2 ^ 59
def prefixEnd_1767754 : Nat := 4983230072969 + 3 ^ 40 * 1767754 * 2
def baseEnd_1767754 : Nat := 907707480908181888045253

theorem tailTrace_1767754 : CollatzResearch.WordTrace tailWord_1767754 prefixEnd_1767754 907707480908181888045253 := by
  unfold tailWord_1767754
  simp only [CollatzResearch.WordTrace]
  refine ⟨16118821309434160298039579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42983523491824427461438877 16118821309434160298039579)
  ·
    refine ⟨24178231964151240447059369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16118821309434160298039579 24178231964151240447059369)
    ·
      refine ⟨18133673973113430335294527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24178231964151240447059369 18133673973113430335294527)
      ·
        refine ⟨27200510959670145502941791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18133673973113430335294527 27200510959670145502941791)
        ·
          refine ⟨40800766439505218254412687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27200510959670145502941791 40800766439505218254412687)
          ·
            refine ⟨61201149659257827381619031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40800766439505218254412687 61201149659257827381619031)
            ·
              refine ⟨91801724488886741072428547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61201149659257827381619031 91801724488886741072428547)
              ·
                refine ⟨137702586733330111608642821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91801724488886741072428547 137702586733330111608642821)
                ·
                  refine ⟨25819235012499395926620529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137702586733330111608642821 25819235012499395926620529)
                  ·
                    refine ⟨19364426259374546944965397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25819235012499395926620529 19364426259374546944965397)
                    ·
                      refine ⟨907707480908181888045253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19364426259374546944965397 907707480908181888045253)
                      ·
                        rfl

theorem cell23_1767754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_1767754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767754 prefixEnd_1767754 := by exact prefixLift 1767754
  have htrace : WordTrace (prefixWord ++ tailWord_1767754) baseStart_1767754 baseEnd_1767754 := by
    simpa [prefixWord, tailWord_1767754, baseEnd_1767754] using wordTrace_append hprefix tailTrace_1767754
  have hstable : (prefixWord ++ tailWord_1767754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767754).length < 2 ^ (prefixWord ++ tailWord_1767754).sum := by decide
  have hdescent : baseEnd_1767754 < baseStart_1767754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767762 : List Nat := [3, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2]
def baseStart_1767762 : Nat := 118140960795 + 1767762 * 2 ^ 59
def prefixEnd_1767762 : Nat := 4983230072969 + 3 ^ 40 * 1767762 * 2
def baseEnd_1767762 : Nat := 907711588753417856745217

theorem tailTrace_1767762 : CollatzResearch.WordTrace tailWord_1767762 prefixEnd_1767762 907711588753417856745217 := by
  unfold tailWord_1767762
  simp only [CollatzResearch.WordTrace]
  refine ⟨16118894255426914639612385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42983718014471772372299693 16118894255426914639612385)
  ·
    refine ⟨12089170691570185979709289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16118894255426914639612385 12089170691570185979709289)
    ·
      refine ⟨9066878018677639484781967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12089170691570185979709289 9066878018677639484781967)
      ·
        refine ⟨13600317028016459227172951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9066878018677639484781967 13600317028016459227172951)
        ·
          refine ⟨20400475542024688840759427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13600317028016459227172951 20400475542024688840759427)
          ·
            refine ⟨30600713313037033261139141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20400475542024688840759427 30600713313037033261139141)
            ·
              refine ⟨5737633746194443736463589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30600713313037033261139141 5737633746194443736463589)
              ·
                refine ⟨1075806327411458200586923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5737633746194443736463589 1075806327411458200586923)
                ·
                  refine ⟨1613709491117187300880385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1075806327411458200586923 1613709491117187300880385)
                  ·
                    refine ⟨1210282118337890475660289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1613709491117187300880385 1210282118337890475660289)
                    ·
                      refine ⟨907711588753417856745217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1210282118337890475660289 907711588753417856745217)
                      ·
                        rfl

theorem cell23_1767762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_1767762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767762 prefixEnd_1767762 := by exact prefixLift 1767762
  have htrace : WordTrace (prefixWord ++ tailWord_1767762) baseStart_1767762 baseEnd_1767762 := by
    simpa [prefixWord, tailWord_1767762, baseEnd_1767762] using wordTrace_append hprefix tailTrace_1767762
  have hstable : (prefixWord ++ tailWord_1767762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767762).length < 2 ^ (prefixWord ++ tailWord_1767762).sum := by decide
  have hdescent : baseEnd_1767762 < baseStart_1767762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767772 : List Nat := [2, 2, 4, 3, 2, 1, 1, 1, 1, 6]
def baseStart_1767772 : Nat := 118140960795 + 1767772 * 2 ^ 59
def prefixEnd_1767772 : Nat := 4983230072969 + 3 ^ 40 * 1767772 * 2
def baseEnd_1767772 : Nat := 302572241186654272540057

theorem tailTrace_1767772 : CollatzResearch.WordTrace tailWord_1767772 prefixEnd_1767772 302572241186654272540057 := by
  unfold tailWord_1767772
  simp only [CollatzResearch.WordTrace]
  refine ⟨32237970875835715133156785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42983961167780953510875713 32237970875835715133156785)
  ·
    refine ⟨24178478156876786349867589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32237970875835715133156785 24178478156876786349867589)
    ·
      refine ⟨4533464654414397440600173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24178478156876786349867589 4533464654414397440600173)
      ·
        refine ⟨1700049245405399040225065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4533464654414397440600173 1700049245405399040225065)
        ·
          refine ⟨1275036934054049280168799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1700049245405399040225065 1275036934054049280168799)
          ·
            refine ⟨1912555401081073920253199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275036934054049280168799 1912555401081073920253199)
            ·
              refine ⟨2868833101621610880379799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1912555401081073920253199 2868833101621610880379799)
              ·
                refine ⟨4303249652432416320569699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2868833101621610880379799 4303249652432416320569699)
                ·
                  refine ⟨6454874478648624480854549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4303249652432416320569699 6454874478648624480854549)
                  ·
                    refine ⟨302572241186654272540057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6454874478648624480854549 302572241186654272540057)
                    ·
                      rfl

theorem cell23_1767772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_1767772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767772 prefixEnd_1767772 := by exact prefixLift 1767772
  have htrace : WordTrace (prefixWord ++ tailWord_1767772) baseStart_1767772 baseEnd_1767772 := by
    simpa [prefixWord, tailWord_1767772, baseEnd_1767772] using wordTrace_append hprefix tailTrace_1767772
  have hstable : (prefixWord ++ tailWord_1767772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767772).length < 2 ^ (prefixWord ++ tailWord_1767772).sum := by decide
  have hdescent : baseEnd_1767772 < baseStart_1767772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767805 : List Nat := [1, 4, 1, 1, 2, 3, 2, 3, 1, 3, 2]
def baseStart_1767805 : Nat := 118140960795 + 1767805 * 2 ^ 59
def prefixEnd_1767805 : Nat := 4983230072969 + 3 ^ 40 * 1767805 * 2
def baseEnd_1767805 : Nat := 907733668421561188507519

theorem tailTrace_1767805 : CollatzResearch.WordTrace tailWord_1767805 prefixEnd_1767805 907733668421561188507519 := by
  unfold tailWord_1767805
  simp only [CollatzResearch.WordTrace]
  refine ⟨64477145360551876902264869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42984763573701251268176579 64477145360551876902264869)
  ·
    refine ⟨12089464755103476919174663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64477145360551876902264869 12089464755103476919174663)
    ·
      refine ⟨18134197132655215378761995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12089464755103476919174663 18134197132655215378761995)
      ·
        refine ⟨27201295698982823068142993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18134197132655215378761995 27201295698982823068142993)
        ·
          refine ⟨20400971774237117301107245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27201295698982823068142993 20400971774237117301107245)
          ·
            refine ⟨7650364415338918987915217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20400971774237117301107245 7650364415338918987915217)
            ·
              refine ⟨5737773311504189240936413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7650364415338918987915217 5737773311504189240936413)
              ·
                refine ⟨2151664991814070965351155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5737773311504189240936413 2151664991814070965351155)
                ·
                  refine ⟨3227497487721106448026733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151664991814070965351155 3227497487721106448026733)
                  ·
                    refine ⟨1210311557895414918010025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3227497487721106448026733 1210311557895414918010025)
                    ·
                      refine ⟨907733668421561188507519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1210311557895414918010025 907733668421561188507519)
                      ·
                        rfl

theorem cell23_1767805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_1767805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767805 prefixEnd_1767805 := by exact prefixLift 1767805
  have htrace : WordTrace (prefixWord ++ tailWord_1767805) baseStart_1767805 baseEnd_1767805 := by
    simpa [prefixWord, tailWord_1767805, baseEnd_1767805] using wordTrace_append hprefix tailTrace_1767805
  have hstable : (prefixWord ++ tailWord_1767805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767805).length < 2 ^ (prefixWord ++ tailWord_1767805).sum := by decide
  have hdescent : baseEnd_1767805 < baseStart_1767805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767824 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 13]
def baseStart_1767824 : Nat := 118140960795 + 1767824 * 2 ^ 59
def prefixEnd_1767824 : Nat := 4983230072969 + 3 ^ 40 * 1767824 * 2
def baseEnd_1767824 : Nat := 100860380505999623796659

theorem tailTrace_1767824 : CollatzResearch.WordTrace tailWord_1767824 prefixEnd_1767824 100860380505999623796659 := by
  unfold tailWord_1767824
  simp only [CollatzResearch.WordTrace]
  refine ⟨32238919173741521573603263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42985225564988695431471017 32238919173741521573603263)
  ·
    refine ⟨48358378760612282360404895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32238919173741521573603263 48358378760612282360404895)
    ·
      refine ⟨72537568140918423540607343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48358378760612282360404895 72537568140918423540607343)
      ·
        refine ⟨108806352211377635310911015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72537568140918423540607343 108806352211377635310911015)
        ·
          refine ⟨163209528317066452966366523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108806352211377635310911015 163209528317066452966366523)
          ·
            refine ⟨244814292475599679449549785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163209528317066452966366523 244814292475599679449549785)
            ·
              refine ⟨183610719356699759587162339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244814292475599679449549785 183610719356699759587162339)
              ·
                refine ⟨275416079035049639380743509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183610719356699759587162339 275416079035049639380743509)
                ·
                  refine ⟨100860380505999623796659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 275416079035049639380743509 100860380505999623796659)
                  ·
                    rfl

theorem cell23_1767824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 13].length) (baseStart_1767824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767824 prefixEnd_1767824 := by exact prefixLift 1767824
  have htrace : WordTrace (prefixWord ++ tailWord_1767824) baseStart_1767824 baseEnd_1767824 := by
    simpa [prefixWord, tailWord_1767824, baseEnd_1767824] using wordTrace_append hprefix tailTrace_1767824
  have hstable : (prefixWord ++ tailWord_1767824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767824).length < 2 ^ (prefixWord ++ tailWord_1767824).sum := by decide
  have hdescent : baseEnd_1767824 < baseStart_1767824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767831 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 4]
def baseStart_1767831 : Nat := 118140960795 + 1767831 * 2 ^ 59
def prefixEnd_1767831 : Nat := 4983230072969 + 3 ^ 40 * 1767831 * 2
def baseEnd_1767831 : Nat := 907747018918578086782399

theorem tailTrace_1767831 : CollatzResearch.WordTrace tailWord_1767831 prefixEnd_1767831 907747018918578086782399 := by
  unfold tailWord_1767831
  simp only [CollatzResearch.WordTrace]
  refine ⟨64478093658457683342711347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42985395772305122228474231 64478093658457683342711347)
  ·
    refine ⟨96717140487686525014067021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64478093658457683342711347 96717140487686525014067021)
    ·
      refine ⟨36268927682882446880275133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96717140487686525014067021 36268927682882446880275133)
      ·
        refine ⟨13600847881080917580103175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36268927682882446880275133 13600847881080917580103175)
        ·
          refine ⟨20401271821621376370154763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13600847881080917580103175 20401271821621376370154763)
          ·
            refine ⟨30601907732432064555232145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20401271821621376370154763 30601907732432064555232145)
            ·
              refine ⟨22951430799324048416424109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30601907732432064555232145 22951430799324048416424109)
              ·
                refine ⟨8606786549746518156159041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22951430799324048416424109 8606786549746518156159041)
                ·
                  refine ⟨6455089912309888617119281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8606786549746518156159041 6455089912309888617119281)
                  ·
                    refine ⟨4841317434232416462839461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6455089912309888617119281 4841317434232416462839461)
                    ·
                      refine ⟨907747018918578086782399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4841317434232416462839461 907747018918578086782399)
                      ·
                        rfl

theorem cell23_1767831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_1767831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767831 prefixEnd_1767831 := by exact prefixLift 1767831
  have htrace : WordTrace (prefixWord ++ tailWord_1767831) baseStart_1767831 baseEnd_1767831 := by
    simpa [prefixWord, tailWord_1767831, baseEnd_1767831] using wordTrace_append hprefix tailTrace_1767831
  have hstable : (prefixWord ++ tailWord_1767831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767831).length < 2 ^ (prefixWord ++ tailWord_1767831).sum := by decide
  have hdescent : baseEnd_1767831 < baseStart_1767831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767858 : List Nat := [3, 2, 1, 1, 1, 1, 4, 5, 5]
def baseStart_1767858 : Nat := 118140960795 + 1767858 * 2 ^ 59
def prefixEnd_1767858 : Nat := 4983230072969 + 3 ^ 40 * 1767858 * 2
def baseEnd_1767858 : Nat := 100862320321805497904975

theorem tailTrace_1767858 : CollatzResearch.WordTrace tailWord_1767858 prefixEnd_1767858 100862320321805497904975 := by
  unfold tailWord_1767858
  simp only [CollatzResearch.WordTrace]
  refine ⟨16119769607339966738486057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42986052286239911302629485 16119769607339966738486057)
  ·
    refine ⟨12089827205504975053864543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16119769607339966738486057 12089827205504975053864543)
    ·
      refine ⟨18134740808257462580796815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12089827205504975053864543 18134740808257462580796815)
      ·
        refine ⟨27202111212386193871195223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18134740808257462580796815 27202111212386193871195223)
        ·
          refine ⟨40803166818579290806792835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27202111212386193871195223 40803166818579290806792835)
          ·
            refine ⟨61204750227868936210189253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40803166818579290806792835 61204750227868936210189253)
            ·
              refine ⟨11475890667725425539410485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61204750227868936210189253 11475890667725425539410485)
              ·
                refine ⟨1075864750099258644319733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11475890667725425539410485 1075864750099258644319733)
                ·
                  refine ⟨100862320321805497904975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1075864750099258644319733 100862320321805497904975)
                  ·
                    rfl

theorem cell23_1767858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_1767858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767858 prefixEnd_1767858 := by exact prefixLift 1767858
  have htrace : WordTrace (prefixWord ++ tailWord_1767858) baseStart_1767858 baseEnd_1767858 := by
    simpa [prefixWord, tailWord_1767858, baseEnd_1767858] using wordTrace_append hprefix tailTrace_1767858
  have hstable : (prefixWord ++ tailWord_1767858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767858).length < 2 ^ (prefixWord ++ tailWord_1767858).sum := by decide
  have hdescent : baseEnd_1767858 < baseStart_1767858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767881 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 1, 2, 5]
def baseStart_1767881 : Nat := 118140960795 + 1767881 * 2 ^ 59
def prefixEnd_1767881 : Nat := 4983230072969 + 3 ^ 40 * 1767881 * 2
def baseEnd_1767881 : Nat := 907772692951302891157169

theorem tailTrace_1767881 : CollatzResearch.WordTrace tailWord_1767881 prefixEnd_1767881 907772692951302891157169 := by
  unfold tailWord_1767881
  simp only [CollatzResearch.WordTrace]
  refine ⟨64479917308276541882031497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42986611538851027921354331 64479917308276541882031497)
  ·
    refine ⟨48359937981207406411523623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64479917308276541882031497 48359937981207406411523623)
    ·
      refine ⟨72539906971811109617285435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48359937981207406411523623 72539906971811109617285435)
      ·
        refine ⟨108809860457716664425928153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72539906971811109617285435 108809860457716664425928153)
        ·
          refine ⟨81607395343287498319446115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108809860457716664425928153 81607395343287498319446115)
          ·
            refine ⟨122411093014931247479169173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81607395343287498319446115 122411093014931247479169173)
            ·
              refine ⟨5738019985074902225586055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122411093014931247479169173 5738019985074902225586055)
              ·
                refine ⟨8607029977612353338379083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5738019985074902225586055 8607029977612353338379083)
                ·
                  refine ⟨12910544966418530007568625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8607029977612353338379083 12910544966418530007568625)
                  ·
                    refine ⟨9682908724813897505676469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12910544966418530007568625 9682908724813897505676469)
                    ·
                      refine ⟨907772692951302891157169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9682908724813897505676469 907772692951302891157169)
                      ·
                        rfl

theorem cell23_1767881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 2, 5].length) (baseStart_1767881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767881 prefixEnd_1767881 := by exact prefixLift 1767881
  have htrace : WordTrace (prefixWord ++ tailWord_1767881) baseStart_1767881 baseEnd_1767881 := by
    simpa [prefixWord, tailWord_1767881, baseEnd_1767881] using wordTrace_append hprefix tailTrace_1767881
  have hstable : (prefixWord ++ tailWord_1767881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767881).length < 2 ^ (prefixWord ++ tailWord_1767881).sum := by decide
  have hdescent : baseEnd_1767881 < baseStart_1767881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767921 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 1, 3, 6]
def baseStart_1767921 : Nat := 118140960795 + 1767921 * 2 ^ 59
def prefixEnd_1767921 : Nat := 4983230072969 + 3 ^ 40 * 1767921 * 2
def baseEnd_1767921 : Nat := 907793232177482734656985

theorem tailTrace_1767921 : CollatzResearch.WordTrace tailWord_1767921 prefixEnd_1767921 907793232177482734656985 := by
  unfold tailWord_1767921
  simp only [CollatzResearch.WordTrace]
  refine ⟨64481376228131628713487617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42987584152087752475658411 64481376228131628713487617)
  ·
    refine ⟨48361032171098721535115713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64481376228131628713487617 48361032171098721535115713)
    ·
      refine ⟨36270774128324041151336785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48361032171098721535115713 36270774128324041151336785)
      ·
        refine ⟨27203080596243030863502589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36270774128324041151336785 27203080596243030863502589)
        ·
          refine ⟨10201155223591136573813471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27203080596243030863502589 10201155223591136573813471)
          ·
            refine ⟨15301732835386704860720207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10201155223591136573813471 15301732835386704860720207)
            ·
              refine ⟨22952599253080057291080311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15301732835386704860720207 22952599253080057291080311)
              ·
                refine ⟨34428898879620085936620467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22952599253080057291080311 34428898879620085936620467)
                ·
                  refine ⟨51643348319430128904930701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34428898879620085936620467 51643348319430128904930701)
                  ·
                    refine ⟨19366255619786298339349013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51643348319430128904930701 19366255619786298339349013)
                    ·
                      refine ⟨907793232177482734656985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19366255619786298339349013 907793232177482734656985)
                      ·
                        rfl

theorem cell23_1767921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_1767921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767921 prefixEnd_1767921 := by exact prefixLift 1767921
  have htrace : WordTrace (prefixWord ++ tailWord_1767921) baseStart_1767921 baseEnd_1767921 := by
    simpa [prefixWord, tailWord_1767921, baseEnd_1767921] using wordTrace_append hprefix tailTrace_1767921
  have hstable : (prefixWord ++ tailWord_1767921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767921).length < 2 ^ (prefixWord ++ tailWord_1767921).sum := by decide
  have hdescent : baseEnd_1767921 < baseStart_1767921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767928 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 4, 2, 3]
def baseStart_1767928 : Nat := 118140960795 + 1767928 * 2 ^ 59
def prefixEnd_1767928 : Nat := 4983230072969 + 3 ^ 40 * 1767928 * 2
def baseEnd_1767928 : Nat := 907796826542064207269453

theorem tailTrace_1767928 : CollatzResearch.WordTrace tailWord_1767928 prefixEnd_1767928 907796826542064207269453 := by
  unfold tailWord_1767928
  simp only [CollatzResearch.WordTrace]
  refine ⟨32240815769553134454496219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42987754359404179272661625 32240815769553134454496219)
  ·
    refine ⟨48361223654329701681744329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32240815769553134454496219 48361223654329701681744329)
    ·
      refine ⟨36270917740747276261308247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48361223654329701681744329 36270917740747276261308247)
      ·
        refine ⟨54406376611120914391962371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36270917740747276261308247 54406376611120914391962371)
        ·
          refine ⟨81609564916681371587943557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54406376611120914391962371 81609564916681371587943557)
          ·
            refine ⟨15301793421877757172739417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81609564916681371587943557 15301793421877757172739417)
            ·
              refine ⟨11476345066408317879554563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15301793421877757172739417 11476345066408317879554563)
              ·
                refine ⟨17214517599612476819331845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11476345066408317879554563 17214517599612476819331845)
                ·
                  refine ⟨3227722049927339403624721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17214517599612476819331845 3227722049927339403624721)
                  ·
                    refine ⟨2420791537445504552718541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3227722049927339403624721 2420791537445504552718541)
                    ·
                      refine ⟨907796826542064207269453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2420791537445504552718541 907796826542064207269453)
                      ·
                        rfl

theorem cell23_1767928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_1767928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767928 prefixEnd_1767928 := by exact prefixLift 1767928
  have htrace : WordTrace (prefixWord ++ tailWord_1767928) baseStart_1767928 baseEnd_1767928 := by
    simpa [prefixWord, tailWord_1767928, baseEnd_1767928] using wordTrace_append hprefix tailTrace_1767928
  have hstable : (prefixWord ++ tailWord_1767928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767928).length < 2 ^ (prefixWord ++ tailWord_1767928).sum := by decide
  have hdescent : baseEnd_1767928 < baseStart_1767928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767935 : List Nat := [1, 1, 2, 2, 1, 2, 3, 6, 1, 4]
def baseStart_1767935 : Nat := 118140960795 + 1767935 * 2 ^ 59
def prefixEnd_1767935 : Nat := 4983230072969 + 3 ^ 40 * 1767935 * 2
def baseEnd_1767935 : Nat := 302600140302215226627307

theorem tailTrace_1767935 : CollatzResearch.WordTrace tailWord_1767935 prefixEnd_1767935 302600140302215226627307 := by
  unfold tailWord_1767935
  simp only [CollatzResearch.WordTrace]
  refine ⟨64481886850080909104497259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42987924566720606069664839 64481886850080909104497259)
  ·
    refine ⟨96722830275121363656745889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64481886850080909104497259 96722830275121363656745889)
    ·
      refine ⟨72542122706341022742559417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96722830275121363656745889 72542122706341022742559417)
      ·
        refine ⟨54406592029755767056919563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72542122706341022742559417 54406592029755767056919563)
        ·
          refine ⟨81609888044633650585379345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54406592029755767056919563 81609888044633650585379345)
          ·
            refine ⟨61207416033475237939034509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81609888044633650585379345 61207416033475237939034509)
            ·
              refine ⟨22952781012553214227137941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61207416033475237939034509 22952781012553214227137941)
              ·
                refine ⟨1075911609963431916897091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22952781012553214227137941 1075911609963431916897091)
                ·
                  refine ⟨1613867414945147875345637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1075911609963431916897091 1613867414945147875345637)
                  ·
                    refine ⟨302600140302215226627307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1613867414945147875345637 302600140302215226627307)
                    ·
                      rfl

theorem cell23_1767935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 1, 4].length) (baseStart_1767935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767935 prefixEnd_1767935 := by exact prefixLift 1767935
  have htrace : WordTrace (prefixWord ++ tailWord_1767935) baseStart_1767935 baseEnd_1767935 := by
    simpa [prefixWord, tailWord_1767935, baseEnd_1767935] using wordTrace_append hprefix tailTrace_1767935
  have hstable : (prefixWord ++ tailWord_1767935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767935).length < 2 ^ (prefixWord ++ tailWord_1767935).sum := by decide
  have hdescent : baseEnd_1767935 < baseStart_1767935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767985 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 4, 3, 2]
def baseStart_1767985 : Nat := 118140960795 + 1767985 * 2 ^ 59
def prefixEnd_1767985 : Nat := 4983230072969 + 3 ^ 40 * 1767985 * 2
def baseEnd_1767985 : Nat := 907826094939370484256691

theorem tailTrace_1767985 : CollatzResearch.WordTrace tailWord_1767985 prefixEnd_1767985 907826094939370484256691 := by
  unfold tailWord_1767985
  simp only [CollatzResearch.WordTrace]
  refine ⟨64483710499899767643817409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42989140333266511762544939 64483710499899767643817409)
  ·
    refine ⟨48362782874924825732863057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64483710499899767643817409 48362782874924825732863057)
    ·
      refine ⟨36272087156193619299647293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48362782874924825732863057 36272087156193619299647293)
      ·
        refine ⟨13602032683572607237367735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36272087156193619299647293 13602032683572607237367735)
        ·
          refine ⟨20403049025358910856051603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13602032683572607237367735 20403049025358910856051603)
          ·
            refine ⟨30604573538038366284077405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20403049025358910856051603 30604573538038366284077405)
            ·
              refine ⟨11476715076764387356529027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30604573538038366284077405 11476715076764387356529027)
              ·
                refine ⟨17215072615146581034793541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11476715076764387356529027 17215072615146581034793541)
                ·
                  refine ⟨3227826115339983944023789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17215072615146581034793541 3227826115339983944023789)
                  ·
                    refine ⟨1210434793252493979008921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3227826115339983944023789 1210434793252493979008921)
                    ·
                      refine ⟨907826094939370484256691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1210434793252493979008921 907826094939370484256691)
                      ·
                        rfl

theorem cell23_1767985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_1767985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1767985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1767985 prefixEnd_1767985 := by exact prefixLift 1767985
  have htrace : WordTrace (prefixWord ++ tailWord_1767985) baseStart_1767985 baseEnd_1767985 := by
    simpa [prefixWord, tailWord_1767985, baseEnd_1767985] using wordTrace_append hprefix tailTrace_1767985
  have hstable : (prefixWord ++ tailWord_1767985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767985).length < 2 ^ (prefixWord ++ tailWord_1767985).sum := by decide
  have hdescent : baseEnd_1767985 < baseStart_1767985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768015 : List Nat := [1, 1, 2, 1, 1, 2, 7, 2, 1, 1, 4]
def baseStart_1768015 : Nat := 118140960795 + 1768015 * 2 ^ 59
def prefixEnd_1768015 : Nat := 4983230072969 + 3 ^ 40 * 1768015 * 2
def baseEnd_1768015 : Nat := 907841499359005366881553

theorem tailTrace_1768015 : CollatzResearch.WordTrace tailWord_1768015 prefixEnd_1768015 907841499359005366881553 := by
  unfold tailWord_1768015
  simp only [CollatzResearch.WordTrace]
  refine ⟨64484804689791082767409499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42989869793194055178272999 64484804689791082767409499)
  ·
    refine ⟨96727207034686624151114249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64484804689791082767409499 96727207034686624151114249)
    ·
      refine ⟨72545405276014968113335687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96727207034686624151114249 72545405276014968113335687)
      ·
        refine ⟨108818107914022452170003531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72545405276014968113335687 108818107914022452170003531)
        ·
          refine ⟨163227161871033678255005297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108818107914022452170003531 163227161871033678255005297)
          ·
            refine ⟨122420371403275258691253973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163227161871033678255005297 122420371403275258691253973)
            ·
              refine ⟨2869227454764263875576265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 122420371403275258691253973 2869227454764263875576265)
              ·
                refine ⟨2151920591073197906682199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2869227454764263875576265 2151920591073197906682199)
                ·
                  refine ⟨3227880886609796860023299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151920591073197906682199 3227880886609796860023299)
                  ·
                    refine ⟨4841821329914695290034949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3227880886609796860023299 4841821329914695290034949)
                    ·
                      refine ⟨907841499359005366881553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4841821329914695290034949 907841499359005366881553)
                      ·
                        rfl

theorem cell23_1768015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 1, 4].length) (baseStart_1768015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768015 prefixEnd_1768015 := by exact prefixLift 1768015
  have htrace : WordTrace (prefixWord ++ tailWord_1768015) baseStart_1768015 baseEnd_1768015 := by
    simpa [prefixWord, tailWord_1768015, baseEnd_1768015] using wordTrace_append hprefix tailTrace_1768015
  have hstable : (prefixWord ++ tailWord_1768015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768015).length < 2 ^ (prefixWord ++ tailWord_1768015).sum := by decide
  have hdescent : baseEnd_1768015 < baseStart_1768015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768042 : List Nat := [3, 1, 3, 2, 1, 1, 4, 2, 2, 4]
def baseStart_1768042 : Nat := 118140960795 + 1768042 * 2 ^ 59
def prefixEnd_1768042 : Nat := 4983230072969 + 3 ^ 40 * 1768042 * 2
def baseEnd_1768042 : Nat := 302618454445558920414643

theorem tailTrace_1768042 : CollatzResearch.WordTrace tailWord_1768042 prefixEnd_1768042 302618454445558920414643 := by
  unfold tailWord_1768042
  simp only [CollatzResearch.WordTrace]
  refine ⟨16121447365173316594660595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42990526307128844252428253 16121447365173316594660595)
  ·
    refine ⟨24182171047759974891990893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16121447365173316594660595 24182171047759974891990893)
    ·
      refine ⟨9068314142909990584496585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24182171047759974891990893 9068314142909990584496585)
      ·
        refine ⟨6801235607182492938372439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9068314142909990584496585 6801235607182492938372439)
        ·
          refine ⟨10201853410773739407558659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6801235607182492938372439 10201853410773739407558659)
          ·
            refine ⟨15302780116160609111337989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10201853410773739407558659 15302780116160609111337989)
            ·
              refine ⟨2869271271780114208375873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15302780116160609111337989 2869271271780114208375873)
              ·
                refine ⟨2151953453835085656281905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2869271271780114208375873 2151953453835085656281905)
                ·
                  refine ⟨1613965090376314242211429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2151953453835085656281905 1613965090376314242211429)
                  ·
                    refine ⟨302618454445558920414643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1613965090376314242211429 302618454445558920414643)
                    ·
                      rfl

theorem cell23_1768042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_1768042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768042 prefixEnd_1768042 := by exact prefixLift 1768042
  have htrace : WordTrace (prefixWord ++ tailWord_1768042) baseStart_1768042 baseEnd_1768042 := by
    simpa [prefixWord, tailWord_1768042, baseEnd_1768042] using wordTrace_append hprefix tailTrace_1768042
  have hstable : (prefixWord ++ tailWord_1768042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768042).length < 2 ^ (prefixWord ++ tailWord_1768042).sum := by decide
  have hdescent : baseEnd_1768042 < baseStart_1768042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768082 : List Nat := [3, 2, 3, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_1768082 : Nat := 118140960795 + 1768082 * 2 ^ 59
def prefixEnd_1768082 : Nat := 4983230072969 + 3 ^ 40 * 1768082 * 2
def baseEnd_1768082 : Nat := 907875902562856604743745

theorem tailTrace_1768082 : CollatzResearch.WordTrace tailWord_1768082 prefixEnd_1768082 907875902562856604743745 := by
  unfold tailWord_1768082
  simp only [CollatzResearch.WordTrace]
  refine ⟨16121812095137088302524625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42991498920365568806732333 16121812095137088302524625)
  ·
    refine ⟨12091359071352816226893469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16121812095137088302524625 12091359071352816226893469)
    ·
      refine ⟨4534259651757306085085051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12091359071352816226893469 4534259651757306085085051)
      ·
        refine ⟨6801389477635959127627577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4534259651757306085085051 6801389477635959127627577)
        ·
          refine ⟨5101042108226969345720683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6801389477635959127627577 5101042108226969345720683)
          ·
            refine ⟨7651563162340454018581025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5101042108226969345720683 7651563162340454018581025)
            ·
              refine ⟨5738672371755340513935769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7651563162340454018581025 5738672371755340513935769)
              ·
                refine ⟨4304004278816505385451827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5738672371755340513935769 4304004278816505385451827)
                ·
                  refine ⟨6456006418224758078177741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4304004278816505385451827 6456006418224758078177741)
                  ·
                    refine ⟨2421002406834284279316653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6456006418224758078177741 2421002406834284279316653)
                    ·
                      refine ⟨907875902562856604743745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2421002406834284279316653 907875902562856604743745)
                      ·
                        rfl

theorem cell23_1768082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_1768082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768082 prefixEnd_1768082 := by exact prefixLift 1768082
  have htrace : WordTrace (prefixWord ++ tailWord_1768082) baseStart_1768082 baseEnd_1768082 := by
    simpa [prefixWord, tailWord_1768082, baseEnd_1768082] using wordTrace_append hprefix tailTrace_1768082
  have hstable : (prefixWord ++ tailWord_1768082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768082).length < 2 ^ (prefixWord ++ tailWord_1768082).sum := by decide
  have hdescent : baseEnd_1768082 < baseStart_1768082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768105 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 5, 4, 2]
def baseStart_1768105 : Nat := 118140960795 + 1768105 * 2 ^ 59
def prefixEnd_1768105 : Nat := 4983230072969 + 3 ^ 40 * 1768105 * 2
def baseEnd_1768105 : Nat := 907887712617910014756139

theorem tailTrace_1768105 : CollatzResearch.WordTrace tailWord_1768105 prefixEnd_1768105 907887712617910014756139 := by
  unfold tailWord_1768105
  simp only [CollatzResearch.WordTrace]
  refine ⟨64488087259465028138185769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42992058172976685425457179 64488087259465028138185769)
  ·
    refine ⟨48366065444598771103639327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64488087259465028138185769 48366065444598771103639327)
    ·
      refine ⟨72549098166898156655458991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48366065444598771103639327 72549098166898156655458991)
      ·
        refine ⟨108823647250347234983188487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72549098166898156655458991 108823647250347234983188487)
        ·
          refine ⟨163235470875520852474782731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108823647250347234983188487 163235470875520852474782731)
          ·
            refine ⟨244853206313281278712174097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163235470875520852474782731 244853206313281278712174097)
            ·
              refine ⟨183639904734960959034130573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244853206313281278712174097 183639904734960959034130573)
              ·
                refine ⟨68864964275610359637798965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183639904734960959034130573 68864964275610359637798965)
                ·
                  refine ⟨6456090400838471216043653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68864964275610359637798965 6456090400838471216043653)
                  ·
                    refine ⟨1210516950157213353008185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6456090400838471216043653 1210516950157213353008185)
                    ·
                      refine ⟨907887712617910014756139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1210516950157213353008185 907887712617910014756139)
                      ·
                        rfl

theorem cell23_1768105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 4, 2].length) (baseStart_1768105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768105 prefixEnd_1768105 := by exact prefixLift 1768105
  have htrace : WordTrace (prefixWord ++ tailWord_1768105) baseStart_1768105 baseEnd_1768105 := by
    simpa [prefixWord, tailWord_1768105, baseEnd_1768105] using wordTrace_append hprefix tailTrace_1768105
  have hstable : (prefixWord ++ tailWord_1768105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768105).length < 2 ^ (prefixWord ++ tailWord_1768105).sum := by decide
  have hdescent : baseEnd_1768105 < baseStart_1768105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768134 : List Nat := [6, 1, 2, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_1768134 : Nat := 118140960795 + 1768134 * 2 ^ 59
def prefixEnd_1768134 : Nat := 4983230072969 + 3 ^ 40 * 1768134 * 2
def baseEnd_1768134 : Nat := 907902603556890401293507

theorem tailTrace_1768134 : CollatzResearch.WordTrace tailWord_1768134 prefixEnd_1768134 907902603556890401293507 := by
  unfold tailWord_1768134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2015285780511248940343483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42992763317573310727327637 2015285780511248940343483)
  ·
    refine ⟨3022928670766873410515225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2015285780511248940343483 3022928670766873410515225)
    ·
      refine ⟨2267196503075155057886419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3022928670766873410515225 2267196503075155057886419)
      ·
        refine ⟨3400794754612732586829629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2267196503075155057886419 3400794754612732586829629)
        ·
          refine ⟨1275298032979774720061111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3400794754612732586829629 1275298032979774720061111)
          ·
            refine ⟨1912947049469662080091667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275298032979774720061111 1912947049469662080091667)
            ·
              refine ⟨2869420574204493120137501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1912947049469662080091667 2869420574204493120137501)
              ·
                refine ⟨1076032715326684920051563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2869420574204493120137501 1076032715326684920051563)
                ·
                  refine ⟨1614049072990027380077345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1076032715326684920051563 1614049072990027380077345)
                  ·
                    refine ⟨1210536804742520535058009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1614049072990027380077345 1210536804742520535058009)
                    ·
                      refine ⟨907902603556890401293507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1210536804742520535058009 907902603556890401293507)
                      ·
                        rfl

theorem cell23_1768134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_1768134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768134 prefixEnd_1768134 := by exact prefixLift 1768134
  have htrace : WordTrace (prefixWord ++ tailWord_1768134) baseStart_1768134 baseEnd_1768134 := by
    simpa [prefixWord, tailWord_1768134, baseEnd_1768134] using wordTrace_append hprefix tailTrace_1768134
  have hstable : (prefixWord ++ tailWord_1768134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768134).length < 2 ^ (prefixWord ++ tailWord_1768134).sum := by decide
  have hdescent : baseEnd_1768134 < baseStart_1768134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768156 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_1768156 : Nat := 118140960795 + 1768156 * 2 ^ 59
def prefixEnd_1768156 : Nat := 4983230072969 + 3 ^ 40 * 1768156 * 2
def baseEnd_1768156 : Nat := 907913900131289315218405

theorem tailTrace_1768156 : CollatzResearch.WordTrace tailWord_1768156 prefixEnd_1768156 907913900131289315218405 := by
  unfold tailWord_1768156
  simp only [CollatzResearch.WordTrace]
  refine ⟨32244973691140131924146161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42993298254853509232194881 32244973691140131924146161)
  ·
    refine ⟨24183730268355098943109621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32244973691140131924146161 24183730268355098943109621)
    ·
      refine ⟨2267224712658290525916527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24183730268355098943109621 2267224712658290525916527)
      ·
        refine ⟨3400837068987435788874791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2267224712658290525916527 3400837068987435788874791)
        ·
          refine ⟨5101255603481153683312187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3400837068987435788874791 5101255603481153683312187)
          ·
            refine ⟨7651883405221730524968281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5101255603481153683312187 7651883405221730524968281)
            ·
              refine ⟨5738912553916297893726211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7651883405221730524968281 5738912553916297893726211)
              ·
                refine ⟨8608368830874446840589317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5738912553916297893726211 8608368830874446840589317)
                ·
                  refine ⟨1614069155788958782610497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8608368830874446840589317 1614069155788958782610497)
                  ·
                    refine ⟨1210551866841719086957873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1614069155788958782610497 1210551866841719086957873)
                    ·
                      refine ⟨907913900131289315218405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1210551866841719086957873 907913900131289315218405)
                      ·
                        rfl

theorem cell23_1768156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_1768156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768156 prefixEnd_1768156 := by exact prefixLift 1768156
  have htrace : WordTrace (prefixWord ++ tailWord_1768156) baseStart_1768156 baseEnd_1768156 := by
    simpa [prefixWord, tailWord_1768156, baseEnd_1768156] using wordTrace_append hprefix tailTrace_1768156
  have hstable : (prefixWord ++ tailWord_1768156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768156).length < 2 ^ (prefixWord ++ tailWord_1768156).sum := by decide
  have hdescent : baseEnd_1768156 < baseStart_1768156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768232 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_1768232 : Nat := 118140960795 + 1768232 * 2 ^ 59
def prefixEnd_1768232 : Nat := 4983230072969 + 3 ^ 40 * 1768232 * 2
def baseEnd_1768232 : Nat := 907952924661031017868055

theorem tailTrace_1768232 : CollatzResearch.WordTrace tailWord_1768232 prefixEnd_1768232 907952924661031017868055 := by
  unfold tailWord_1768232
  simp only [CollatzResearch.WordTrace]
  refine ⟨32246359665002464414029475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42995146220003285885372633 32246359665002464414029475)
  ·
    refine ⟨48369539497503696621044213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32246359665002464414029475 48369539497503696621044213)
    ·
      refine ⟨4534644327890971558222895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48369539497503696621044213 4534644327890971558222895)
      ·
        refine ⟨6801966491836457337334343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4534644327890971558222895 6801966491836457337334343)
        ·
          refine ⟨10202949737754686006001515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6801966491836457337334343 10202949737754686006001515)
          ·
            refine ⟨15304424606632029009002273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10202949737754686006001515 15304424606632029009002273)
            ·
              refine ⟨11478318454974021756751705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15304424606632029009002273 11478318454974021756751705)
              ·
                refine ⟨8608738841230516317563779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11478318454974021756751705 8608738841230516317563779)
                ·
                  refine ⟨12913108261845774476345669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8608738841230516317563779 12913108261845774476345669)
                  ·
                    refine ⟨2421207799096082714314813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12913108261845774476345669 2421207799096082714314813)
                    ·
                      refine ⟨907952924661031017868055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2421207799096082714314813 907952924661031017868055)
                      ·
                        rfl

theorem cell23_1768232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_1768232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768232 prefixEnd_1768232 := by exact prefixLift 1768232
  have htrace : WordTrace (prefixWord ++ tailWord_1768232) baseStart_1768232 baseEnd_1768232 := by
    simpa [prefixWord, tailWord_1768232, baseEnd_1768232] using wordTrace_append hprefix tailTrace_1768232
  have hstable : (prefixWord ++ tailWord_1768232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768232).length < 2 ^ (prefixWord ++ tailWord_1768232).sum := by decide
  have hdescent : baseEnd_1768232 < baseStart_1768232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768269 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 8]
def baseStart_1768269 : Nat := 118140960795 + 1768269 * 2 ^ 59
def prefixEnd_1768269 : Nat := 4983230072969 + 3 ^ 40 * 1768269 * 2
def baseEnd_1768269 : Nat := 100885769271694152567265

theorem tailTrace_1768269 : CollatzResearch.WordTrace tailWord_1768269 prefixEnd_1768269 100885769271694152567265 := by
  unfold tailWord_1768269
  simp only [CollatzResearch.WordTrace]
  refine ⟨64494068830870884147155861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42996045887247256098103907 64494068830870884147155861)
  ·
    refine ⟨3023159476447072694397931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 64494068830870884147155861 3023159476447072694397931)
    ·
      refine ⟨4534739214670609041596897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3023159476447072694397931 4534739214670609041596897)
      ·
        refine ⟨3401054411002956781197673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4534739214670609041596897 3401054411002956781197673)
        ·
          refine ⟨2550790808252217585898255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3401054411002956781197673 2550790808252217585898255)
          ·
            refine ⟨3826186212378326378847383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2550790808252217585898255 3826186212378326378847383)
            ·
              refine ⟨5739279318567489568271075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3826186212378326378847383 5739279318567489568271075)
              ·
                refine ⟨8608918977851234352406613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5739279318567489568271075 8608918977851234352406613)
                ·
                  refine ⟨100885769271694152567265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8608918977851234352406613 100885769271694152567265)
                  ·
                    rfl

theorem cell23_1768269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_1768269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768269 prefixEnd_1768269 := by exact prefixLift 1768269
  have htrace : WordTrace (prefixWord ++ tailWord_1768269) baseStart_1768269 baseEnd_1768269 := by
    simpa [prefixWord, tailWord_1768269, baseEnd_1768269] using wordTrace_append hprefix tailTrace_1768269
  have hstable : (prefixWord ++ tailWord_1768269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768269).length < 2 ^ (prefixWord ++ tailWord_1768269).sum := by decide
  have hdescent : baseEnd_1768269 < baseStart_1768269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768279 : List Nat := [1, 1, 3, 2, 4, 1, 1, 3, 3, 1, 3]
def baseStart_1768279 : Nat := 118140960795 + 1768279 * 2 ^ 59
def prefixEnd_1768279 : Nat := 4983230072969 + 3 ^ 40 * 1768279 * 2
def baseEnd_1768279 : Nat := 907977058251792333980339

theorem tailTrace_1768279 : CollatzResearch.WordTrace tailWord_1768279 prefixEnd_1768279 907977058251792333980339 := by
  unfold tailWord_1768279
  simp only [CollatzResearch.WordTrace]
  refine ⟨64494433560834655855019891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42996289040556437236679927 64494433560834655855019891)
  ·
    refine ⟨96741650341251983782529837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64494433560834655855019891 96741650341251983782529837)
    ·
      refine ⟨36278118877969493918448689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96741650341251983782529837 36278118877969493918448689)
      ·
        refine ⟨27208589158477120438836517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36278118877969493918448689 27208589158477120438836517)
        ·
          refine ⟨5101610467214460082281847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27208589158477120438836517 5101610467214460082281847)
          ·
            refine ⟨7652415700821690123422771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5101610467214460082281847 7652415700821690123422771)
            ·
              refine ⟨11478623551232535185134157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7652415700821690123422771 11478623551232535185134157)
              ·
                refine ⟨4304483831712200694425309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11478623551232535185134157 4304483831712200694425309)
                ·
                  refine ⟨1614181436892075260409491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4304483831712200694425309 1614181436892075260409491)
                  ·
                    refine ⟨2421272155338112890614237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1614181436892075260409491 2421272155338112890614237)
                    ·
                      refine ⟨907977058251792333980339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2421272155338112890614237 907977058251792333980339)
                      ·
                        rfl

theorem cell23_1768279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_1768279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768279 prefixEnd_1768279 := by exact prefixLift 1768279
  have htrace : WordTrace (prefixWord ++ tailWord_1768279) baseStart_1768279 baseEnd_1768279 := by
    simpa [prefixWord, tailWord_1768279, baseEnd_1768279] using wordTrace_append hprefix tailTrace_1768279
  have hstable : (prefixWord ++ tailWord_1768279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768279).length < 2 ^ (prefixWord ++ tailWord_1768279).sum := by decide
  have hdescent : baseEnd_1768279 < baseStart_1768279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768313 : List Nat := [1, 2, 1, 3, 2, 5, 1, 3, 1, 1, 3]
def baseStart_1768313 : Nat := 118140960795 + 1768313 * 2 ^ 59
def prefixEnd_1768313 : Nat := 4983230072969 + 3 ^ 40 * 1768313 * 2
def baseEnd_1768313 : Nat := 907994516594045200955183

theorem tailTrace_1768313 : CollatzResearch.WordTrace tailWord_1768313 prefixEnd_1768313 907994516594045200955183 := by
  unfold tailWord_1768313
  simp only [CollatzResearch.WordTrace]
  refine ⟨64495673642711479661757593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42997115761807653107838395 64495673642711479661757593)
  ·
    refine ⟨48371755232033609746318195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64495673642711479661757593 48371755232033609746318195)
    ·
      refine ⟨72557632848050414619477293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48371755232033609746318195 72557632848050414619477293)
      ·
        refine ⟨27209112318018905482303985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72557632848050414619477293 27209112318018905482303985)
        ·
          refine ⟨20406834238514179111727989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27209112318018905482303985 20406834238514179111727989)
          ·
            refine ⟨1913140709860704291724499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20406834238514179111727989 1913140709860704291724499)
            ·
              refine ⟨2869711064791056437586749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1913140709860704291724499 2869711064791056437586749)
              ·
                refine ⟨1076141649296646164095031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2869711064791056437586749 1076141649296646164095031)
                ·
                  refine ⟨1614212473944969246142547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1076141649296646164095031 1614212473944969246142547)
                  ·
                    refine ⟨2421318710917453869213821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1614212473944969246142547 2421318710917453869213821)
                    ·
                      refine ⟨907994516594045200955183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2421318710917453869213821 907994516594045200955183)
                      ·
                        rfl

theorem cell23_1768313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 1, 1, 3].length) (baseStart_1768313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768313 prefixEnd_1768313 := by exact prefixLift 1768313
  have htrace : WordTrace (prefixWord ++ tailWord_1768313) baseStart_1768313 baseEnd_1768313 := by
    simpa [prefixWord, tailWord_1768313, baseEnd_1768313] using wordTrace_append hprefix tailTrace_1768313
  have hstable : (prefixWord ++ tailWord_1768313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768313).length < 2 ^ (prefixWord ++ tailWord_1768313).sum := by decide
  have hdescent : baseEnd_1768313 < baseStart_1768313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
