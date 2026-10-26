import V185TrunkScan23Chunk1076

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6376479 : List Nat := [1, 1, 2, 4, 1, 4, 2, 2, 1, 2, 3]
def baseStart_6376479 : Nat := 118140960795 + 6376479 * 2 ^ 59
def prefixEnd_6376479 : Nat := 4983230072969 + 3 ^ 40 * 6376479 * 2
def baseEnd_6376479 : Nat := 3274198610300662730287613

theorem tailTrace_6376479 : CollatzResearch.WordTrace tailWord_6376479 prefixEnd_6376479 3274198610300662730287613 := by
  unfold tailWord_6376479
  simp only [CollatzResearch.WordTrace]
  refine ⟨232569295466113073757324491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155046196977408715838216327 232569295466113073757324491)
  ·
    refine ⟨348853943199169610635986737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232569295466113073757324491 348853943199169610635986737)
    ·
      refine ⟨261640457399377207976990053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348853943199169610635986737 261640457399377207976990053)
      ·
        refine ⟨49057585762383226495685635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261640457399377207976990053 49057585762383226495685635)
        ·
          refine ⟨73586378643574839743528453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49057585762383226495685635 73586378643574839743528453)
          ·
            refine ⟨13797445995670282451911585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73586378643574839743528453 13797445995670282451911585)
            ·
              refine ⟨10348084496752711838933689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13797445995670282451911585 10348084496752711838933689)
              ·
                refine ⟨7761063372564533879200267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10348084496752711838933689 7761063372564533879200267)
                ·
                  refine ⟨11641595058846800818800401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7761063372564533879200267 11641595058846800818800401)
                  ·
                    refine ⟨8731196294135100614100301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11641595058846800818800401 8731196294135100614100301)
                    ·
                      refine ⟨3274198610300662730287613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8731196294135100614100301 3274198610300662730287613)
                      ·
                        rfl

theorem cell23_6376479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_6376479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376479 prefixEnd_6376479 := by exact prefixLift 6376479
  have htrace : WordTrace (prefixWord ++ tailWord_6376479) baseStart_6376479 baseEnd_6376479 := by
    simpa [prefixWord, tailWord_6376479, baseEnd_6376479] using wordTrace_append hprefix tailTrace_6376479
  have hstable : (prefixWord ++ tailWord_6376479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376479).length < 2 ^ (prefixWord ++ tailWord_6376479).sum := by decide
  have hdescent : baseEnd_6376479 < baseStart_6376479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376482 : List Nat := [3, 3, 1, 1, 1, 3, 4, 7]
def baseStart_6376482 : Nat := 118140960795 + 6376482 * 2 ^ 59
def prefixEnd_6376482 : Nat := 4983230072969 + 3 ^ 40 * 6376482 * 2
def baseEnd_6376482 : Nat := 121266672249726896983337

theorem tailTrace_6376482 : CollatzResearch.WordTrace tailWord_6376482 prefixEnd_6376482 121266672249726896983337 := by
  unfold tailWord_6376482
  simp only [CollatzResearch.WordTrace]
  refine ⟨58142351221275551317420925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155046269923401470179789133 58142351221275551317420925)
  ·
    refine ⟨21803381707978331744032847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58142351221275551317420925 21803381707978331744032847)
    ·
      refine ⟨32705072561967497616049271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21803381707978331744032847 32705072561967497616049271)
      ·
        refine ⟨49057608842951246424073907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32705072561967497616049271 49057608842951246424073907)
        ·
          refine ⟨73586413264426869636110861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49057608842951246424073907 73586413264426869636110861)
          ·
            refine ⟨27594904974160076113541573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73586413264426869636110861 27594904974160076113541573)
            ·
              refine ⟨5174044682655014271289045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27594904974160076113541573 5174044682655014271289045)
              ·
                refine ⟨121266672249726896983337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5174044682655014271289045 121266672249726896983337)
                ·
                  rfl

theorem cell23_6376482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 7].length) (baseStart_6376482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376482 prefixEnd_6376482 := by exact prefixLift 6376482
  have htrace : WordTrace (prefixWord ++ tailWord_6376482) baseStart_6376482 baseEnd_6376482 := by
    simpa [prefixWord, tailWord_6376482, baseEnd_6376482] using wordTrace_append hprefix tailTrace_6376482
  have hstable : (prefixWord ++ tailWord_6376482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376482).length < 2 ^ (prefixWord ++ tailWord_6376482).sum := by decide
  have hdescent : baseEnd_6376482 < baseStart_6376482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376492 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 3]
def baseStart_6376492 : Nat := 118140960795 + 6376492 * 2 ^ 59
def prefixEnd_6376492 : Nat := 4983230072969 + 3 ^ 40 * 6376492 * 2
def baseEnd_6376492 : Nat := 3274205285549171179425053

theorem tailTrace_6376492 : CollatzResearch.WordTrace tailWord_6376492 prefixEnd_6376492 3274205285549171179425053 := by
  unfold tailWord_6376492
  simp only [CollatzResearch.WordTrace]
  refine ⟨116284884807532988488773865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155046513076710651318365153 116284884807532988488773865)
  ·
    refine ⟨87213663605649741366580399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116284884807532988488773865 87213663605649741366580399)
    ·
      refine ⟨130820495408474612049870599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87213663605649741366580399 130820495408474612049870599)
      ·
        refine ⟨196230743112711918074805899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130820495408474612049870599 196230743112711918074805899)
        ·
          refine ⟨294346114669067877112208849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196230743112711918074805899 294346114669067877112208849)
          ·
            refine ⟨220759586001800907834156637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294346114669067877112208849 220759586001800907834156637)
            ·
              refine ⟨82784844750675340437808739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220759586001800907834156637 82784844750675340437808739)
              ·
                refine ⟨124177267126013010656713109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82784844750675340437808739 124177267126013010656713109)
                ·
                  refine ⟨5820809396531859874533427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124177267126013010656713109 5820809396531859874533427)
                  ·
                    refine ⟨8731214094797789811800141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5820809396531859874533427 8731214094797789811800141)
                    ·
                      refine ⟨3274205285549171179425053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8731214094797789811800141 3274205285549171179425053)
                      ·
                        rfl

theorem cell23_6376492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 3].length) (baseStart_6376492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376492 prefixEnd_6376492 := by exact prefixLift 6376492
  have htrace : WordTrace (prefixWord ++ tailWord_6376492) baseStart_6376492 baseEnd_6376492 := by
    simpa [prefixWord, tailWord_6376492, baseEnd_6376492] using wordTrace_append hprefix tailTrace_6376492
  have hstable : (prefixWord ++ tailWord_6376492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376492).length < 2 ^ (prefixWord ++ tailWord_6376492).sum := by decide
  have hdescent : baseEnd_6376492 < baseStart_6376492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376509 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 4, 1, 3]
def baseStart_6376509 : Nat := 118140960795 + 6376509 * 2 ^ 59
def prefixEnd_6376509 : Nat := 4983230072969 + 3 ^ 40 * 6376509 * 2
def baseEnd_6376509 : Nat := 3274214014720297612912475

theorem tailTrace_6376509 : CollatzResearch.WordTrace tailWord_6376509 prefixEnd_6376509 3274214014720297612912475 := by
  unfold tailWord_6376509
  simp only [CollatzResearch.WordTrace]
  refine ⟨232570389656004388880916581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155046926437336259253944387 232570389656004388880916581)
  ·
    refine ⟨43606948060500822915171859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232570389656004388880916581 43606948060500822915171859)
    ·
      refine ⟨65410422090751234372757789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43606948060500822915171859 65410422090751234372757789)
      ·
        refine ⟨24528908284031712889784171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65410422090751234372757789 24528908284031712889784171)
        ·
          refine ⟨36793362426047569334676257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24528908284031712889784171 36793362426047569334676257)
          ·
            refine ⟨27595021819535677001007193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36793362426047569334676257 27595021819535677001007193)
            ·
              refine ⟨20696266364651757750755395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27595021819535677001007193 20696266364651757750755395)
              ·
                refine ⟨31044399546977636626133093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20696266364651757750755395 31044399546977636626133093)
                ·
                  refine ⟨5820824915058306867399955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31044399546977636626133093 5820824915058306867399955)
                  ·
                    refine ⟨8731237372587460301099933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5820824915058306867399955 8731237372587460301099933)
                    ·
                      refine ⟨3274214014720297612912475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8731237372587460301099933 3274214014720297612912475)
                      ·
                        rfl

theorem cell23_6376509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_6376509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376509 prefixEnd_6376509 := by exact prefixLift 6376509
  have htrace : WordTrace (prefixWord ++ tailWord_6376509) baseStart_6376509 baseEnd_6376509 := by
    simpa [prefixWord, tailWord_6376509, baseEnd_6376509] using wordTrace_append hprefix tailTrace_6376509
  have hstable : (prefixWord ++ tailWord_6376509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376509).length < 2 ^ (prefixWord ++ tailWord_6376509).sum := by decide
  have hdescent : baseEnd_6376509 < baseStart_6376509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376515 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 4]
def baseStart_6376515 : Nat := 118140960795 + 6376515 * 2 ^ 59
def prefixEnd_6376515 : Nat := 4983230072969 + 3 ^ 40 * 6376515 * 2
def baseEnd_6376515 : Nat := 3274217095604224589437447

theorem tailTrace_6376515 : CollatzResearch.WordTrace tailWord_6376515 prefixEnd_6376515 3274217095604224589437447 := by
  unfold tailWord_6376515
  simp only [CollatzResearch.WordTrace]
  refine ⟨232570608493982651905634999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155047072329321767937089999 232570608493982651905634999)
  ·
    refine ⟨348855912740973977858452499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232570608493982651905634999 348855912740973977858452499)
    ·
      refine ⟨523283869111460966787678749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348855912740973977858452499 523283869111460966787678749)
      ·
        refine ⟨196231450916797862545379531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 523283869111460966787678749 196231450916797862545379531)
        ·
          refine ⟨294347176375196793818069297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196231450916797862545379531 294347176375196793818069297)
          ·
            refine ⟨220760382281397595363551973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294347176375196793818069297 220760382281397595363551973)
            ·
              refine ⟨41392571677762049130665995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 220760382281397595363551973 41392571677762049130665995)
              ·
                refine ⟨62088857516643073695998993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41392571677762049130665995 62088857516643073695998993)
                ·
                  refine ⟨46566643137482305271999245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62088857516643073695998993 46566643137482305271999245)
                  ·
                    refine ⟨17462491176555864476999717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46566643137482305271999245 17462491176555864476999717)
                    ·
                      refine ⟨3274217095604224589437447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17462491176555864476999717 3274217095604224589437447)
                      ·
                        rfl

theorem cell23_6376515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_6376515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376515 prefixEnd_6376515 := by exact prefixLift 6376515
  have htrace : WordTrace (prefixWord ++ tailWord_6376515) baseStart_6376515 baseEnd_6376515 := by
    simpa [prefixWord, tailWord_6376515, baseEnd_6376515] using wordTrace_append hprefix tailTrace_6376515
  have hstable : (prefixWord ++ tailWord_6376515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376515).length < 2 ^ (prefixWord ++ tailWord_6376515).sum := by decide
  have hdescent : baseEnd_6376515 < baseStart_6376515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376549 : List Nat := [1, 3, 1, 3, 2, 1, 3, 2, 1, 4, 2]
def baseStart_6376549 : Nat := 118140960795 + 6376549 * 2 ^ 59
def prefixEnd_6376549 : Nat := 4983230072969 + 3 ^ 40 * 6376549 * 2
def baseEnd_6376549 : Nat := 3274234553946477456412291

theorem tailTrace_6376549 : CollatzResearch.WordTrace tailWord_6376549 prefixEnd_6376549 3274234553946477456412291 := by
  unfold tailWord_6376549
  simp only [CollatzResearch.WordTrace]
  refine ⟨232571848575859475712372701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155047899050572983808248467 232571848575859475712372701)
  ·
    refine ⟨87214443215947303392139763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232571848575859475712372701 87214443215947303392139763)
    ·
      refine ⟨130821664823920955088209645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87214443215947303392139763 130821664823920955088209645)
      ·
        refine ⟨49058124308970358158078617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130821664823920955088209645 49058124308970358158078617)
        ·
          refine ⟨36793593231727768618558963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49058124308970358158078617 36793593231727768618558963)
          ·
            refine ⟨55190389847591652927838445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36793593231727768618558963 55190389847591652927838445)
            ·
              refine ⟨20696396192846869847939417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55190389847591652927838445 20696396192846869847939417)
              ·
                refine ⟨15522297144635152385954563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20696396192846869847939417 15522297144635152385954563)
                ·
                  refine ⟨23283445716952728578931845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15522297144635152385954563 23283445716952728578931845)
                  ·
                    refine ⟨4365646071928636608549721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23283445716952728578931845 4365646071928636608549721)
                    ·
                      refine ⟨3274234553946477456412291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4365646071928636608549721 3274234553946477456412291)
                      ·
                        rfl

theorem cell23_6376549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_6376549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376549 prefixEnd_6376549 := by exact prefixLift 6376549
  have htrace : WordTrace (prefixWord ++ tailWord_6376549) baseStart_6376549 baseEnd_6376549 := by
    simpa [prefixWord, tailWord_6376549, baseEnd_6376549] using wordTrace_append hprefix tailTrace_6376549
  have hstable : (prefixWord ++ tailWord_6376549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376549).length < 2 ^ (prefixWord ++ tailWord_6376549).sum := by decide
  have hdescent : baseEnd_6376549 < baseStart_6376549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376562 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_6376562 : Nat := 118140960795 + 6376562 * 2 ^ 59
def prefixEnd_6376562 : Nat := 4983230072969 + 3 ^ 40 * 6376562 * 2
def baseEnd_6376562 : Nat := 3274241229194985905549731

theorem tailTrace_6376562 : CollatzResearch.WordTrace tailWord_6376562 prefixEnd_6376562 3274241229194985905549731 := by
  unfold tailWord_6376562
  simp only [CollatzResearch.WordTrace]
  refine ⟨58143080681203094733148985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155048215149874919288397293 58143080681203094733148985)
  ·
    refine ⟨43607310510902321049861739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58143080681203094733148985 43607310510902321049861739)
    ·
      refine ⟨65410965766353481574792609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43607310510902321049861739 65410965766353481574792609)
      ·
        refine ⟨49058224324765111181094457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65410965766353481574792609 49058224324765111181094457)
        ·
          refine ⟨36793668243573833385820843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49058224324765111181094457 36793668243573833385820843)
          ·
            refine ⟨55190502365360750078731265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36793668243573833385820843 55190502365360750078731265)
            ·
              refine ⟨41392876774020562559048449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55190502365360750078731265 41392876774020562559048449)
              ·
                refine ⟨31044657580515421919286337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41392876774020562559048449 31044657580515421919286337)
                ·
                  refine ⟨23283493185386566439464753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31044657580515421919286337 23283493185386566439464753)
                  ·
                    refine ⟨17462619889039924829598565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23283493185386566439464753 17462619889039924829598565)
                    ·
                      refine ⟨3274241229194985905549731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17462619889039924829598565 3274241229194985905549731)
                      ·
                        rfl

theorem cell23_6376562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_6376562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376562 prefixEnd_6376562 := by exact prefixLift 6376562
  have htrace : WordTrace (prefixWord ++ tailWord_6376562) baseStart_6376562 baseEnd_6376562 := by
    simpa [prefixWord, tailWord_6376562, baseEnd_6376562] using wordTrace_append hprefix tailTrace_6376562
  have hstable : (prefixWord ++ tailWord_6376562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376562).length < 2 ^ (prefixWord ++ tailWord_6376562).sum := by decide
  have hdescent : baseEnd_6376562 < baseStart_6376562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376595 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 7]
def baseStart_6376595 : Nat := 118140960795 + 6376595 * 2 ^ 59
def prefixEnd_6376595 : Nat := 4983230072969 + 3 ^ 40 * 6376595 * 2
def baseEnd_6376595 : Nat := 3274258174056584276437079

theorem tailTrace_6376595 : CollatzResearch.WordTrace tailWord_6376595 prefixEnd_6376595 3274258174056584276437079 := by
  unfold tailWord_6376595
  simp only [CollatzResearch.WordTrace]
  refine ⟨232573526333692825568547239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155049017555795217045698159 232573526333692825568547239)
  ·
    refine ⟨348860289500539238352820859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232573526333692825568547239 348860289500539238352820859)
    ·
      refine ⟨523290434250808857529231289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348860289500539238352820859 523290434250808857529231289)
      ·
        refine ⟨392467825688106643146923467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523290434250808857529231289 392467825688106643146923467)
        ·
          refine ⟨588701738532159964720385201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392467825688106643146923467 588701738532159964720385201)
          ·
            refine ⟨441526303899119973540288901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588701738532159964720385201 441526303899119973540288901)
            ·
              refine ⟨82786181981084995038804169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 441526303899119973540288901 82786181981084995038804169)
              ·
                refine ⟨62089636485813746279103127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82786181981084995038804169 62089636485813746279103127)
                ·
                  refine ⟨93134454728720619418654691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62089636485813746279103127 93134454728720619418654691)
                  ·
                    refine ⟨139701682093080929127982037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93134454728720619418654691 139701682093080929127982037)
                    ·
                      refine ⟨3274258174056584276437079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139701682093080929127982037 3274258174056584276437079)
                      ·
                        rfl

theorem cell23_6376595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_6376595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376595 prefixEnd_6376595 := by exact prefixLift 6376595
  have htrace : WordTrace (prefixWord ++ tailWord_6376595) baseStart_6376595 baseEnd_6376595 := by
    simpa [prefixWord, tailWord_6376595, baseEnd_6376595] using wordTrace_append hprefix tailTrace_6376595
  have hstable : (prefixWord ++ tailWord_6376595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376595).length < 2 ^ (prefixWord ++ tailWord_6376595).sum := by decide
  have hdescent : baseEnd_6376595 < baseStart_6376595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376606 : List Nat := [4, 3, 1, 1, 2, 1, 1, 5, 5]
def baseStart_6376606 : Nat := 118140960795 + 6376606 * 2 ^ 59
def prefixEnd_6376606 : Nat := 4983230072969 + 3 ^ 40 * 6376606 * 2
def baseEnd_6376606 : Nat := 363807091371531525933281

theorem tailTrace_6376606 : CollatzResearch.WordTrace tailWord_6376606 prefixEnd_6376606 363807091371531525933281 := by
  unfold tailWord_6376606
  simp only [CollatzResearch.WordTrace]
  refine ⟨29071740942081621805899709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155049285024435316298131781 29071740942081621805899709)
  ·
    refine ⟨10901902853280608177212391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29071740942081621805899709 10901902853280608177212391)
    ·
      refine ⟨16352854279920912265818587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10901902853280608177212391 16352854279920912265818587)
      ·
        refine ⟨24529281419881368398727881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16352854279920912265818587 24529281419881368398727881)
        ·
          refine ⟨18396961064911026299045911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24529281419881368398727881 18396961064911026299045911)
          ·
            refine ⟨27595441597366539448568867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18396961064911026299045911 27595441597366539448568867)
            ·
              refine ⟨41393162396049809172853301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27595441597366539448568867 41393162396049809172853301)
              ·
                refine ⟨3880608974629669609954997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41393162396049809172853301 3880608974629669609954997)
                ·
                  refine ⟨363807091371531525933281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3880608974629669609954997 363807091371531525933281)
                  ·
                    rfl

theorem cell23_6376606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_6376606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376606 prefixEnd_6376606 := by exact prefixLift 6376606
  have htrace : WordTrace (prefixWord ++ tailWord_6376606) baseStart_6376606 baseEnd_6376606 := by
    simpa [prefixWord, tailWord_6376606, baseEnd_6376606] using wordTrace_append hprefix tailTrace_6376606
  have hstable : (prefixWord ++ tailWord_6376606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376606).length < 2 ^ (prefixWord ++ tailWord_6376606).sum := by decide
  have hdescent : baseEnd_6376606 < baseStart_6376606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376639 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 2, 4, 2]
def baseStart_6376639 : Nat := 118140960795 + 6376639 * 2 ^ 59
def prefixEnd_6376639 : Nat := 4983230072969 + 3 ^ 40 * 6376639 * 2
def baseEnd_6376639 : Nat := 3274280767205382104286877

theorem tailTrace_6376639 : CollatzResearch.WordTrace tailWord_6376639 prefixEnd_6376639 3274280767205382104286877 := by
  unfold tailWord_6376639
  simp only [CollatzResearch.WordTrace]
  refine ⟨232575131145533421083148971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155050087430355614055432647 232575131145533421083148971)
  ·
    refine ⟨348862696718300131624723457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232575131145533421083148971 348862696718300131624723457)
    ·
      refine ⟨261647022538725098718542593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348862696718300131624723457 261647022538725098718542593)
      ·
        refine ⟨196235266904043824038906945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261647022538725098718542593 196235266904043824038906945)
        ·
          refine ⟨147176450178032868029180209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196235266904043824038906945 147176450178032868029180209)
          ·
            refine ⟨110382337633524651021885157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147176450178032868029180209 110382337633524651021885157)
            ·
              refine ⟨20696688306285872066603467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110382337633524651021885157 20696688306285872066603467)
              ·
                refine ⟨31045032459428808099905201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20696688306285872066603467 31045032459428808099905201)
                ·
                  refine ⟨23283774344571606074928901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31045032459428808099905201 23283774344571606074928901)
                  ·
                    refine ⟨4365707689607176139049169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23283774344571606074928901 4365707689607176139049169)
                    ·
                      refine ⟨3274280767205382104286877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4365707689607176139049169 3274280767205382104286877)
                      ·
                        rfl

theorem cell23_6376639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 4, 2].length) (baseStart_6376639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376639 prefixEnd_6376639 := by exact prefixLift 6376639
  have htrace : WordTrace (prefixWord ++ tailWord_6376639) baseStart_6376639 baseEnd_6376639 := by
    simpa [prefixWord, tailWord_6376639, baseEnd_6376639] using wordTrace_append hprefix tailTrace_6376639
  have hstable : (prefixWord ++ tailWord_6376639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376639).length < 2 ^ (prefixWord ++ tailWord_6376639).sum := by decide
  have hdescent : baseEnd_6376639 < baseStart_6376639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376683 : List Nat := [1, 1, 1, 1, 2, 7, 3, 2, 1, 4]
def baseStart_6376683 : Nat := 118140960795 + 6376683 * 2 ^ 59
def prefixEnd_6376683 : Nat := 4983230072969 + 3 ^ 40 * 6376683 * 2
def baseEnd_6376683 : Nat := 1091434453451393310712225

theorem tailTrace_6376683 : CollatzResearch.WordTrace tailWord_6376683 prefixEnd_6376683 1091434453451393310712225 := by
  unfold tailWord_6376683
  simp only [CollatzResearch.WordTrace]
  refine ⟨232576735957374016597750703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155051157304916011065167135 232576735957374016597750703)
  ·
    refine ⟨348865103936061024896626055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232576735957374016597750703 348865103936061024896626055)
    ·
      refine ⟨523297655904091537344939083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348865103936061024896626055 523297655904091537344939083)
      ·
        refine ⟨784946483856137306017408625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523297655904091537344939083 784946483856137306017408625)
        ·
          refine ⟨588709862892102979513056469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 784946483856137306017408625 588709862892102979513056469)
          ·
            refine ⟨13797887411533663582337261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 588709862892102979513056469 13797887411533663582337261)
            ·
              refine ⟨5174207779325123843376473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13797887411533663582337261 5174207779325123843376473)
              ·
                refine ⟨3880655834493842882532355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5174207779325123843376473 3880655834493842882532355)
                ·
                  refine ⟨5820983751740764323798533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3880655834493842882532355 5820983751740764323798533)
                  ·
                    refine ⟨1091434453451393310712225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5820983751740764323798533 1091434453451393310712225)
                    ·
                      rfl

theorem cell23_6376683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 1, 4].length) (baseStart_6376683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376683 prefixEnd_6376683 := by exact prefixLift 6376683
  have htrace : WordTrace (prefixWord ++ tailWord_6376683) baseStart_6376683 baseEnd_6376683 := by
    simpa [prefixWord, tailWord_6376683, baseEnd_6376683] using wordTrace_append hprefix tailTrace_6376683
  have hstable : (prefixWord ++ tailWord_6376683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376683).length < 2 ^ (prefixWord ++ tailWord_6376683).sum := by decide
  have hdescent : baseEnd_6376683 < baseStart_6376683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376716 : List Nat := [2, 2, 1, 2, 2, 3, 1, 3, 2, 3, 2]
def baseStart_6376716 : Nat := 118140960795 + 6376716 * 2 ^ 59
def prefixEnd_6376716 : Nat := 4983230072969 + 3 ^ 40 * 6376716 * 2
def baseEnd_6376716 : Nat := 3274320305215778303024023

theorem tailTrace_6376716 : CollatzResearch.WordTrace tailWord_6376716 prefixEnd_6376716 3274320305215778303024023 := by
  unfold tailWord_6376716
  simp only [CollatzResearch.WordTrace]
  refine ⟨116288969783127231616851001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155051959710836308822468001 116288969783127231616851001)
  ·
    refine ⟨87216727337345423712638251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116288969783127231616851001 87216727337345423712638251)
    ·
      refine ⟨130825091006018135568957377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87216727337345423712638251 130825091006018135568957377)
      ·
        refine ⟨98118818254513601676718033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130825091006018135568957377 98118818254513601676718033)
        ·
          refine ⟨73589113690885201257538525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98118818254513601676718033 73589113690885201257538525)
          ·
            refine ⟨27595917634081950471576947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73589113690885201257538525 27595917634081950471576947)
            ·
              refine ⟨41393876451122925707365421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27595917634081950471576947 41393876451122925707365421)
              ·
                refine ⟨15522703669171097140262033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41393876451122925707365421 15522703669171097140262033)
                ·
                  refine ⟨11642027751878322855196525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15522703669171097140262033 11642027751878322855196525)
                  ·
                    refine ⟨4365760406954371070698697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11642027751878322855196525 4365760406954371070698697)
                    ·
                      refine ⟨3274320305215778303024023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4365760406954371070698697 3274320305215778303024023)
                      ·
                        rfl

theorem cell23_6376716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_6376716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376716 prefixEnd_6376716 := by exact prefixLift 6376716
  have htrace : WordTrace (prefixWord ++ tailWord_6376716) baseStart_6376716 baseEnd_6376716 := by
    simpa [prefixWord, tailWord_6376716, baseEnd_6376716] using wordTrace_append hprefix tailTrace_6376716
  have hstable : (prefixWord ++ tailWord_6376716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376716).length < 2 ^ (prefixWord ++ tailWord_6376716).sum := by decide
  have hdescent : baseEnd_6376716 < baseStart_6376716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376733 : List Nat := [1, 4, 2, 3, 1, 1, 2, 2, 2, 3, 2]
def baseStart_6376733 : Nat := 118140960795 + 6376733 * 2 ^ 59
def prefixEnd_6376733 : Nat := 4983230072969 + 3 ^ 40 * 6376733 * 2
def baseEnd_6376733 : Nat := 3274329034386904736511445

theorem tailTrace_6376733 : CollatzResearch.WordTrace tailWord_6376733 prefixEnd_6376733 3274329034386904736511445 := by
  unfold tailWord_6376733
  simp only [CollatzResearch.WordTrace]
  refine ⟨232578559607192875137070853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155052373071461916758047235 232578559607192875137070853)
  ·
    refine ⟨43608479926348664088200785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232578559607192875137070853 43608479926348664088200785)
    ·
      refine ⟨32706359944761498066150589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43608479926348664088200785 32706359944761498066150589)
      ·
        refine ⟨12264884979285561774806471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32706359944761498066150589 12264884979285561774806471)
        ·
          refine ⟨18397327468928342662209707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12264884979285561774806471 18397327468928342662209707)
          ·
            refine ⟨27595991203392513993314561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18397327468928342662209707 27595991203392513993314561)
            ·
              refine ⟨20696993402544385494985921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27595991203392513993314561 20696993402544385494985921)
              ·
                refine ⟨15522745051908289121239441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20696993402544385494985921 15522745051908289121239441)
                ·
                  refine ⟨11642058788931216840929581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15522745051908289121239441 11642058788931216840929581)
                  ·
                    refine ⟨4365772045849206315348593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11642058788931216840929581 4365772045849206315348593)
                    ·
                      refine ⟨3274329034386904736511445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4365772045849206315348593 3274329034386904736511445)
                      ·
                        rfl

theorem cell23_6376733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_6376733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376733 prefixEnd_6376733 := by exact prefixLift 6376733
  have htrace : WordTrace (prefixWord ++ tailWord_6376733) baseStart_6376733 baseEnd_6376733 := by
    simpa [prefixWord, tailWord_6376733, baseEnd_6376733] using wordTrace_append hprefix tailTrace_6376733
  have hstable : (prefixWord ++ tailWord_6376733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376733).length < 2 ^ (prefixWord ++ tailWord_6376733).sum := by decide
  have hdescent : baseEnd_6376733 < baseStart_6376733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376734 : List Nat := [4, 3, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_6376734 : Nat := 118140960795 + 6376734 * 2 ^ 59
def prefixEnd_6376734 : Nat := 4983230072969 + 3 ^ 40 * 6376734 * 2
def baseEnd_6376734 : Nat := 1091443182622519744199647

theorem tailTrace_6376734 : CollatzResearch.WordTrace tailWord_6376734 prefixEnd_6376734 1091443182622519744199647 := by
  unfold tailWord_6376734
  simp only [CollatzResearch.WordTrace]
  refine ⟨29072324510023656538482157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155052397386792834871904837 29072324510023656538482157)
  ·
    refine ⟨10902121691258871201930809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29072324510023656538482157 10902121691258871201930809)
    ·
      refine ⟨8176591268444153401448107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10902121691258871201930809 8176591268444153401448107)
      ·
        refine ⟨12264886902666230102172161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8176591268444153401448107 12264886902666230102172161)
        ·
          refine ⟨9198665176999672576629121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12264886902666230102172161 9198665176999672576629121)
          ·
            refine ⟨6898998882749754432471841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9198665176999672576629121 6898998882749754432471841)
            ·
              refine ⟨5174249162062315824353881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6898998882749754432471841 5174249162062315824353881)
              ·
                refine ⟨3880686871546736868265411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5174249162062315824353881 3880686871546736868265411)
                ·
                  refine ⟨5821030307320105302398117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3880686871546736868265411 5821030307320105302398117)
                  ·
                    refine ⟨1091443182622519744199647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5821030307320105302398117 1091443182622519744199647)
                    ·
                      rfl

theorem cell23_6376734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_6376734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376734 prefixEnd_6376734 := by exact prefixLift 6376734
  have htrace : WordTrace (prefixWord ++ tailWord_6376734) baseStart_6376734 baseEnd_6376734 := by
    simpa [prefixWord, tailWord_6376734, baseEnd_6376734] using wordTrace_append hprefix tailTrace_6376734
  have hstable : (prefixWord ++ tailWord_6376734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376734).length < 2 ^ (prefixWord ++ tailWord_6376734).sum := by decide
  have hdescent : baseEnd_6376734 < baseStart_6376734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376746 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_6376746 : Nat := 118140960795 + 6376746 * 2 ^ 59
def prefixEnd_6376746 : Nat := 4983230072969 + 3 ^ 40 * 6376746 * 2
def baseEnd_6376746 : Nat := 3274335709635413185648885

theorem tailTrace_6376746 : CollatzResearch.WordTrace tailWord_6376746 prefixEnd_6376746 3274335709635413185648885 := by
  unfold tailWord_6376746
  simp only [CollatzResearch.WordTrace]
  refine ⟨58144758439036444589323523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155052689170763852238196061 58144758439036444589323523)
  ·
    refine ⟨87217137658554666883985285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58144758439036444589323523 87217137658554666883985285)
    ·
      refine ⟨16353213310979000040747241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87217137658554666883985285 16353213310979000040747241)
      ·
        refine ⟨12264909983234250030560431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16353213310979000040747241 12264909983234250030560431)
        ·
          refine ⟨18397364974851375045840647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12264909983234250030560431 18397364974851375045840647)
          ·
            refine ⟨27596047462277062568760971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18397364974851375045840647 27596047462277062568760971)
            ·
              refine ⟨41394071193415593853141457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27596047462277062568760971 41394071193415593853141457)
              ·
                refine ⟨31045553395061695389856093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41394071193415593853141457 31045553395061695389856093)
                ·
                  refine ⟨11642082523148135771196035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31045553395061695389856093 11642082523148135771196035)
                  ·
                    refine ⟨17463123784722203656794053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11642082523148135771196035 17463123784722203656794053)
                    ·
                      refine ⟨3274335709635413185648885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17463123784722203656794053 3274335709635413185648885)
                      ·
                        rfl

theorem cell23_6376746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_6376746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376746 prefixEnd_6376746 := by exact prefixLift 6376746
  have htrace : WordTrace (prefixWord ++ tailWord_6376746) baseStart_6376746 baseEnd_6376746 := by
    simpa [prefixWord, tailWord_6376746, baseEnd_6376746] using wordTrace_append hprefix tailTrace_6376746
  have hstable : (prefixWord ++ tailWord_6376746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376746).length < 2 ^ (prefixWord ++ tailWord_6376746).sum := by decide
  have hdescent : baseEnd_6376746 < baseStart_6376746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376756 : List Nat := [2, 5, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_6376756 : Nat := 118140960795 + 6376756 * 2 ^ 59
def prefixEnd_6376756 : Nat := 4983230072969 + 3 ^ 40 * 6376756 * 2
def baseEnd_6376756 : Nat := 1091446948147319382174613

theorem tailTrace_6376756 : CollatzResearch.WordTrace tailWord_6376756 prefixEnd_6376756 1091446948147319382174613 := by
  unfold tailWord_6376756
  simp only [CollatzResearch.WordTrace]
  refine ⟨116289699243054775032579061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155052932324073033376772081 116289699243054775032579061)
  ·
    refine ⟨10902159304036385159304287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116289699243054775032579061 10902159304036385159304287)
    ·
      refine ⟨16353238956054577738956431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10902159304036385159304287 16353238956054577738956431)
      ·
        refine ⟨24529858434081866608434647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16353238956054577738956431 24529858434081866608434647)
        ·
          refine ⟨36794787651122799912651971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24529858434081866608434647 36794787651122799912651971)
          ·
            refine ⟨55192181476684199868977957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36794787651122799912651971 55192181476684199868977957)
            ·
              refine ⟨10348534026878287475433367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55192181476684199868977957 10348534026878287475433367)
              ·
                refine ⟨15522801040317431213150051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10348534026878287475433367 15522801040317431213150051)
                ·
                  refine ⟨23284201560476146819725077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15522801040317431213150051 23284201560476146819725077)
                  ·
                    refine ⟨1091446948147319382174613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23284201560476146819725077 1091446948147319382174613)
                    ·
                      rfl

theorem cell23_6376756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_6376756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376756 prefixEnd_6376756 := by exact prefixLift 6376756
  have htrace : WordTrace (prefixWord ++ tailWord_6376756) baseStart_6376756 baseEnd_6376756 := by
    simpa [prefixWord, tailWord_6376756, baseEnd_6376756] using wordTrace_append hprefix tailTrace_6376756
  have hstable : (prefixWord ++ tailWord_6376756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376756).length < 2 ^ (prefixWord ++ tailWord_6376756).sum := by decide
  have hdescent : baseEnd_6376756 < baseStart_6376756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376766 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_6376766 : Nat := 118140960795 + 6376766 * 2 ^ 59
def prefixEnd_6376766 : Nat := 4983230072969 + 3 ^ 40 * 6376766 * 2
def baseEnd_6376766 : Nat := 3274345979248503107398793

theorem tailTrace_6376766 : CollatzResearch.WordTrace tailWord_6376766 prefixEnd_6376766 3274345979248503107398793 := by
  unfold tailWord_6376766
  simp only [CollatzResearch.WordTrace]
  refine ⟨29072470402009165221627769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155053175477382214515348101 29072470402009165221627769)
  ·
    refine ⟨21804352801506873916220827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29072470402009165221627769 21804352801506873916220827)
    ·
      refine ⟨32706529202260310874331241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21804352801506873916220827 32706529202260310874331241)
      ·
        refine ⟨24529896901695233155748431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32706529202260310874331241 24529896901695233155748431)
        ·
          refine ⟨36794845352542849733622647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24529896901695233155748431 36794845352542849733622647)
          ·
            refine ⟨55192268028814274600433971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36794845352542849733622647 55192268028814274600433971)
            ·
              refine ⟨82788402043221411900650957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55192268028814274600433971 82788402043221411900650957)
              ·
                refine ⟨31045650766208029462744109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82788402043221411900650957 31045650766208029462744109)
                ·
                  refine ⟨11642119037328011048529041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31045650766208029462744109 11642119037328011048529041)
                  ·
                    refine ⟨8731589277996008286396781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11642119037328011048529041 8731589277996008286396781)
                    ·
                      refine ⟨3274345979248503107398793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8731589277996008286396781 3274345979248503107398793)
                      ·
                        rfl

theorem cell23_6376766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_6376766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376766 prefixEnd_6376766 := by exact prefixLift 6376766
  have htrace : WordTrace (prefixWord ++ tailWord_6376766) baseStart_6376766 baseEnd_6376766 := by
    simpa [prefixWord, tailWord_6376766, baseEnd_6376766] using wordTrace_append hprefix tailTrace_6376766
  have hstable : (prefixWord ++ tailWord_6376766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376766).length < 2 ^ (prefixWord ++ tailWord_6376766).sum := by decide
  have hdescent : baseEnd_6376766 < baseStart_6376766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376780 : List Nat := [2, 2, 1, 3, 2, 2, 1, 5, 1, 2, 2]
def baseStart_6376780 : Nat := 118140960795 + 6376780 * 2 ^ 59
def prefixEnd_6376780 : Nat := 4983230072969 + 3 ^ 40 * 6376780 * 2
def baseEnd_6376780 : Nat := 3274353167977666052623729

theorem tailTrace_6376780 : CollatzResearch.WordTrace tailWord_6376780 prefixEnd_6376780 3274353167977666052623729 := by
  unfold tailWord_6376780
  simp only [CollatzResearch.WordTrace]
  refine ⟨116290136919011301082015897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155053515892015068109354529 116290136919011301082015897)
  ·
    refine ⟨87217602689258475811511923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116290136919011301082015897 87217602689258475811511923)
    ·
      refine ⟨130826404033887713717267885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87217602689258475811511923 130826404033887713717267885)
      ·
        refine ⟨49059901512707892643975457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130826404033887713717267885 49059901512707892643975457)
        ·
          refine ⟨36794926134530919482981593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49059901512707892643975457 36794926134530919482981593)
          ·
            refine ⟨27596194600898189612236195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36794926134530919482981593 27596194600898189612236195)
            ·
              refine ⟨41394291901347284418354293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27596194600898189612236195 41394291901347284418354293)
              ·
                refine ⟨3880714865751307914220715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41394291901347284418354293 3880714865751307914220715)
                ·
                  refine ⟨5821072298626961871331073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3880714865751307914220715 5821072298626961871331073)
                  ·
                    refine ⟨4365804223970221403498305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5821072298626961871331073 4365804223970221403498305)
                    ·
                      refine ⟨3274353167977666052623729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4365804223970221403498305 3274353167977666052623729)
                      ·
                        rfl

theorem cell23_6376780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_6376780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376780 prefixEnd_6376780 := by exact prefixLift 6376780
  have htrace : WordTrace (prefixWord ++ tailWord_6376780) baseStart_6376780 baseEnd_6376780 := by
    simpa [prefixWord, tailWord_6376780, baseEnd_6376780] using wordTrace_append hprefix tailTrace_6376780
  have hstable : (prefixWord ++ tailWord_6376780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376780).length < 2 ^ (prefixWord ++ tailWord_6376780).sum := by decide
  have hdescent : baseEnd_6376780 < baseStart_6376780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376810 : List Nat := [3, 1, 3, 3, 3, 1, 1, 1, 1, 2, 4]
def baseStart_6376810 : Nat := 118140960795 + 6376810 * 2 ^ 59
def prefixEnd_6376810 : Nat := 4983230072969 + 3 ^ 40 * 6376810 * 2
def baseEnd_6376810 : Nat := 3274368572397300935248591

theorem tailTrace_6376810 : CollatzResearch.WordTrace tailWord_6376810 prefixEnd_6376810 3274368572397300935248591 := by
  unfold tailWord_6376810
  simp only [CollatzResearch.WordTrace]
  refine ⟨58145342006978479321905971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155054245351942611525082589 58145342006978479321905971)
  ·
    refine ⟨87218013010467718982858957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58145342006978479321905971 87218013010467718982858957)
    ·
      refine ⟨32706754878925394618572109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87218013010467718982858957 32706754878925394618572109)
      ·
        refine ⟨12265033079597022981964541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32706754878925394618572109 12265033079597022981964541)
        ·
          refine ⟨4599387404848883618236703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12265033079597022981964541 4599387404848883618236703)
          ·
            refine ⟨6899081107273325427355055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4599387404848883618236703 6899081107273325427355055)
            ·
              refine ⟨10348621660909988141032583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6899081107273325427355055 10348621660909988141032583)
              ·
                refine ⟨15522932491364982211548875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10348621660909988141032583 15522932491364982211548875)
                ·
                  refine ⟨23284398737047473317323313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15522932491364982211548875 23284398737047473317323313)
                  ·
                    refine ⟨17463299052785604987992485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23284398737047473317323313 17463299052785604987992485)
                    ·
                      refine ⟨3274368572397300935248591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17463299052785604987992485 3274368572397300935248591)
                      ·
                        rfl

theorem cell23_6376810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_6376810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376810 prefixEnd_6376810 := by exact prefixLift 6376810
  have htrace : WordTrace (prefixWord ++ tailWord_6376810) baseStart_6376810 baseEnd_6376810 := by
    simpa [prefixWord, tailWord_6376810, baseEnd_6376810] using wordTrace_append hprefix tailTrace_6376810
  have hstable : (prefixWord ++ tailWord_6376810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376810).length < 2 ^ (prefixWord ++ tailWord_6376810).sum := by decide
  have hdescent : baseEnd_6376810 < baseStart_6376810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376813 : List Nat := [1, 5, 1, 1, 1, 5, 1, 1, 1, 3, 3]
def baseStart_6376813 : Nat := 118140960795 + 6376813 * 2 ^ 59
def prefixEnd_6376813 : Nat := 4983230072969 + 3 ^ 40 * 6376813 * 2
def baseEnd_6376813 : Nat := 3274370112839264423511077

theorem tailTrace_6376813 : CollatzResearch.WordTrace tailWord_6376813 prefixEnd_6376813 3274370112839264423511077 := by
  unfold tailWord_6376813
  simp only [CollatzResearch.WordTrace]
  refine ⟨232581477446903048799983093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155054318297935365866655395 232581477446903048799983093)
  ·
    refine ⟨21804513510647160824998415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232581477446903048799983093 21804513510647160824998415)
    ·
      refine ⟨32706770265970741237497623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21804513510647160824998415 32706770265970741237497623)
      ·
        refine ⟨49060155398956111856246435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32706770265970741237497623 49060155398956111856246435)
        ·
          refine ⟨73590233098434167784369653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49060155398956111856246435 73590233098434167784369653)
          ·
            refine ⟨6899084352978203229784655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73590233098434167784369653 6899084352978203229784655)
            ·
              refine ⟨10348626529467304844676983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6899084352978203229784655 10348626529467304844676983)
              ·
                refine ⟨15522939794200957267015475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10348626529467304844676983 15522939794200957267015475)
                ·
                  refine ⟨23284409691301435900523213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15522939794200957267015475 23284409691301435900523213)
                  ·
                    refine ⟨8731653634238038462696205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23284409691301435900523213 8731653634238038462696205)
                    ·
                      refine ⟨3274370112839264423511077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8731653634238038462696205 3274370112839264423511077)
                      ·
                        rfl

theorem cell23_6376813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_6376813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376813 prefixEnd_6376813 := by exact prefixLift 6376813
  have htrace : WordTrace (prefixWord ++ tailWord_6376813) baseStart_6376813 baseEnd_6376813 := by
    simpa [prefixWord, tailWord_6376813, baseEnd_6376813] using wordTrace_append hprefix tailTrace_6376813
  have hstable : (prefixWord ++ tailWord_6376813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376813).length < 2 ^ (prefixWord ++ tailWord_6376813).sum := by decide
  have hdescent : baseEnd_6376813 < baseStart_6376813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376823 : List Nat := [1, 1, 3, 1, 1, 2, 6, 2, 1, 3, 2]
def baseStart_6376823 : Nat := 118140960795 + 6376823 * 2 ^ 59
def prefixEnd_6376823 : Nat := 4983230072969 + 3 ^ 40 * 6376823 * 2
def baseEnd_6376823 : Nat := 3274375247645809384386031

theorem tailTrace_6376823 : CollatzResearch.WordTrace tailWord_6376823 prefixEnd_6376823 3274375247645809384386031 := by
  unfold tailWord_6376823
  simp only [CollatzResearch.WordTrace]
  refine ⟨232581842176866820507847123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155054561451244547005231415 232581842176866820507847123)
  ·
    refine ⟨348872763265300230761770685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232581842176866820507847123 348872763265300230761770685)
    ·
      refine ⟨130827286224487586535664007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348872763265300230761770685 130827286224487586535664007)
      ·
        refine ⟨196240929336731379803496011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130827286224487586535664007 196240929336731379803496011)
        ·
          refine ⟨294361394005097069705244017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196240929336731379803496011 294361394005097069705244017)
          ·
            refine ⟨220771045503822802278933013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294361394005097069705244017 220771045503822802278933013)
            ·
              refine ⟨10348642757991693856824985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 220771045503822802278933013 10348642757991693856824985)
              ·
                refine ⟨7761482068493770392618739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10348642757991693856824985 7761482068493770392618739)
                ·
                  refine ⟨11642223102740655588928109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7761482068493770392618739 11642223102740655588928109)
                  ·
                    refine ⟨4365833663527745845848041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11642223102740655588928109 4365833663527745845848041)
                    ·
                      refine ⟨3274375247645809384386031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4365833663527745845848041 3274375247645809384386031)
                      ·
                        rfl

theorem cell23_6376823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 3, 2].length) (baseStart_6376823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376823 prefixEnd_6376823 := by exact prefixLift 6376823
  have htrace : WordTrace (prefixWord ++ tailWord_6376823) baseStart_6376823 baseEnd_6376823 := by
    simpa [prefixWord, tailWord_6376823, baseEnd_6376823] using wordTrace_append hprefix tailTrace_6376823
  have hstable : (prefixWord ++ tailWord_6376823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376823).length < 2 ^ (prefixWord ++ tailWord_6376823).sum := by decide
  have hdescent : baseEnd_6376823 < baseStart_6376823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376839 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_6376839 : Nat := 118140960795 + 6376839 * 2 ^ 59
def prefixEnd_6376839 : Nat := 4983230072969 + 3 ^ 40 * 6376839 * 2
def baseEnd_6376839 : Nat := 3274383463336281321785957

theorem tailTrace_6376839 : CollatzResearch.WordTrace tailWord_6376839 prefixEnd_6376839 3274383463336281321785957 := by
  unfold tailWord_6376839
  simp only [CollatzResearch.WordTrace]
  refine ⟨232582425744808855240429571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155054950496539236826953047 232582425744808855240429571)
  ·
    refine ⟨348873638617213282860644357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232582425744808855240429571 348873638617213282860644357)
    ·
      refine ⟨65413807240727490536370817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 348873638617213282860644357 65413807240727490536370817)
      ·
        refine ⟨49060355430545617902278113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65413807240727490536370817 49060355430545617902278113)
        ·
          refine ⟨36795266572909213426708585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49060355430545617902278113 36795266572909213426708585)
          ·
            refine ⟨27596449929681910070031439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36795266572909213426708585 27596449929681910070031439)
            ·
              refine ⟨41394674894522865105047159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27596449929681910070031439 41394674894522865105047159)
              ·
                refine ⟨62092012341784297657570739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41394674894522865105047159 62092012341784297657570739)
                ·
                  refine ⟨93138018512676446486356109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62092012341784297657570739 93138018512676446486356109)
                  ·
                    refine ⟨34926756942253667432383541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93138018512676446486356109 34926756942253667432383541)
                    ·
                      refine ⟨3274383463336281321785957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34926756942253667432383541 3274383463336281321785957)
                      ·
                        rfl

theorem cell23_6376839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_6376839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376839 prefixEnd_6376839 := by exact prefixLift 6376839
  have htrace : WordTrace (prefixWord ++ tailWord_6376839) baseStart_6376839 baseEnd_6376839 := by
    simpa [prefixWord, tailWord_6376839, baseEnd_6376839] using wordTrace_append hprefix tailTrace_6376839
  have hstable : (prefixWord ++ tailWord_6376839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376839).length < 2 ^ (prefixWord ++ tailWord_6376839).sum := by decide
  have hdescent : baseEnd_6376839 < baseStart_6376839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376853 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 4, 2, 2]
def baseStart_6376853 : Nat := 118140960795 + 6376853 * 2 ^ 59
def prefixEnd_6376853 : Nat := 4983230072969 + 3 ^ 40 * 6376853 * 2
def baseEnd_6376853 : Nat := 3274390652065444267010893

theorem tailTrace_6376853 : CollatzResearch.WordTrace tailWord_6376853 prefixEnd_6376853 3274390652065444267010893 := by
  unfold tailWord_6376853
  simp only [CollatzResearch.WordTrace]
  refine ⟨232582936366758135631439213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155055290911172090420959475 232582936366758135631439213)
  ·
    refine ⟨87218601137534300861789705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232582936366758135631439213 87218601137534300861789705)
    ·
      refine ⟨65413950853150725646342279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87218601137534300861789705 65413950853150725646342279)
      ·
        refine ⟨98120926279726088469513419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65413950853150725646342279 98120926279726088469513419)
        ·
          refine ⟨147181389419589132704270129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98120926279726088469513419 147181389419589132704270129)
          ·
            refine ⟨110386042064691849528202597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147181389419589132704270129 110386042064691849528202597)
            ·
              refine ⟨20697382887129721786537987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110386042064691849528202597 20697382887129721786537987)
              ·
                refine ⟨31046074330694582679806981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20697382887129721786537987 31046074330694582679806981)
                ·
                  refine ⟨5821138937005234252463809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31046074330694582679806981 5821138937005234252463809)
                  ·
                    refine ⟨4365854202753925689347857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5821138937005234252463809 4365854202753925689347857)
                    ·
                      refine ⟨3274390652065444267010893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4365854202753925689347857 3274390652065444267010893)
                      ·
                        rfl

theorem cell23_6376853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_6376853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376853 prefixEnd_6376853 := by exact prefixLift 6376853
  have htrace : WordTrace (prefixWord ++ tailWord_6376853) baseStart_6376853 baseEnd_6376853 := by
    simpa [prefixWord, tailWord_6376853, baseEnd_6376853] using wordTrace_append hprefix tailTrace_6376853
  have hstable : (prefixWord ++ tailWord_6376853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376853).length < 2 ^ (prefixWord ++ tailWord_6376853).sum := by decide
  have hdescent : baseEnd_6376853 < baseStart_6376853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376899 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 5]
def baseStart_6376899 : Nat := 118140960795 + 6376899 * 2 ^ 59
def prefixEnd_6376899 : Nat := 4983230072969 + 3 ^ 40 * 6376899 * 2
def baseEnd_6376899 : Nat := 3274414272175551087035681

theorem tailTrace_6376899 : CollatzResearch.WordTrace tailWord_6376899 prefixEnd_6376899 3274414272175551087035681 := by
  unfold tailWord_6376899
  simp only [CollatzResearch.WordTrace]
  refine ⟨232584614124591485487613751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155056409416394323658409167 232584614124591485487613751)
  ·
    refine ⟨348876921186887228231420627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232584614124591485487613751 348876921186887228231420627)
    ·
      refine ⟨523315381780330842347130941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348876921186887228231420627 523315381780330842347130941)
      ·
        refine ⟨196243268167624065880174103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 523315381780330842347130941 196243268167624065880174103)
        ·
          refine ⟨294364902251436098820261155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196243268167624065880174103 294364902251436098820261155)
          ·
            refine ⟨441547353377154148230391733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294364902251436098820261155 441547353377154148230391733)
            ·
              refine ⟨41395064379108201396599225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 441547353377154148230391733 41395064379108201396599225)
              ·
                refine ⟨31046298284331151047449419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41395064379108201396599225 31046298284331151047449419)
                ·
                  refine ⟨46569447426496726571174129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31046298284331151047449419 46569447426496726571174129)
                  ·
                    refine ⟨34927085569872544928380597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46569447426496726571174129 34927085569872544928380597)
                    ·
                      refine ⟨3274414272175551087035681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34927085569872544928380597 3274414272175551087035681)
                      ·
                        rfl

theorem cell23_6376899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_6376899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376899 prefixEnd_6376899 := by exact prefixLift 6376899
  have htrace : WordTrace (prefixWord ++ tailWord_6376899) baseStart_6376899 baseEnd_6376899 := by
    simpa [prefixWord, tailWord_6376899, baseEnd_6376899] using wordTrace_append hprefix tailTrace_6376899
  have hstable : (prefixWord ++ tailWord_6376899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376899).length < 2 ^ (prefixWord ++ tailWord_6376899).sum := by decide
  have hdescent : baseEnd_6376899 < baseStart_6376899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376906 : List Nat := [3, 1, 2, 1, 2, 3, 2, 2, 2, 5]
def baseStart_6376906 : Nat := 118140960795 + 6376906 * 2 ^ 59
def prefixEnd_6376906 : Nat := 4983230072969 + 3 ^ 40 * 6376906 * 2
def baseEnd_6376906 : Nat := 1091472622180044186549383

theorem tailTrace_6376906 : CollatzResearch.WordTrace tailWord_6376906 prefixEnd_6376906 1091472622180044186549383 := by
  unfold tailWord_6376906
  simp only [CollatzResearch.WordTrace]
  refine ⟨58146217358891531420779643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155056579623710750455412381 58146217358891531420779643)
  ·
    refine ⟨87219326038337297131169465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58146217358891531420779643 87219326038337297131169465)
    ·
      refine ⟨65414494528752972848377099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87219326038337297131169465 65414494528752972848377099)
      ·
        refine ⟨98121741793129459272565649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65414494528752972848377099 98121741793129459272565649)
        ·
          refine ⟨73591306344847094454424237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98121741793129459272565649 73591306344847094454424237)
          ·
            refine ⟨27596739879317660420409089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73591306344847094454424237 27596739879317660420409089)
            ·
              refine ⟨20697554909488245315306817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27596739879317660420409089 20697554909488245315306817)
              ·
                refine ⟨15523166182116183986480113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20697554909488245315306817 15523166182116183986480113)
                ·
                  refine ⟨11642374636587137989860085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15523166182116183986480113 11642374636587137989860085)
                  ·
                    refine ⟨1091472622180044186549383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11642374636587137989860085 1091472622180044186549383)
                    ·
                      rfl

theorem cell23_6376906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_6376906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376906 prefixEnd_6376906 := by exact prefixLift 6376906
  have htrace : WordTrace (prefixWord ++ tailWord_6376906) baseStart_6376906 baseEnd_6376906 := by
    simpa [prefixWord, tailWord_6376906, baseEnd_6376906] using wordTrace_append hprefix tailTrace_6376906
  have hstable : (prefixWord ++ tailWord_6376906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376906).length < 2 ^ (prefixWord ++ tailWord_6376906).sum := by decide
  have hdescent : baseEnd_6376906 < baseStart_6376906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376939 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 4]
def baseStart_6376939 : Nat := 118140960795 + 6376939 * 2 ^ 59
def prefixEnd_6376939 : Nat := 4983230072969 + 3 ^ 40 * 6376939 * 2
def baseEnd_6376939 : Nat := 3274434811401730930535497

theorem tailTrace_6376939 : CollatzResearch.WordTrace tailWord_6376939 prefixEnd_6376939 3274434811401730930535497 := by
  unfold tailWord_6376939
  simp only [CollatzResearch.WordTrace]
  refine ⟨232586073044446572319069871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155057382029631048212713247 232586073044446572319069871)
  ·
    refine ⟨348879109566669858478604807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232586073044446572319069871 348879109566669858478604807)
    ·
      refine ⟨523318664350004787717907211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348879109566669858478604807 523318664350004787717907211)
      ·
        refine ⟨784977996525007181576860817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523318664350004787717907211 784977996525007181576860817)
        ·
          refine ⟨588733497393755386182645613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 784977996525007181576860817 588733497393755386182645613)
          ·
            refine ⟨220775061522658269818492105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 588733497393755386182645613 220775061522658269818492105)
            ·
              refine ⟨165581296141993702363869079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220775061522658269818492105 165581296141993702363869079)
              ·
                refine ⟨248371944212990553545803619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165581296141993702363869079 248371944212990553545803619)
                ·
                  refine ⟨372557916319485830318705429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248371944212990553545803619 372557916319485830318705429)
                  ·
                    refine ⟨17463652327475898296189317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 372557916319485830318705429 17463652327475898296189317)
                    ·
                      refine ⟨3274434811401730930535497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17463652327475898296189317 3274434811401730930535497)
                      ·
                        rfl

theorem cell23_6376939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 4].length) (baseStart_6376939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376939 prefixEnd_6376939 := by exact prefixLift 6376939
  have htrace : WordTrace (prefixWord ++ tailWord_6376939) baseStart_6376939 baseEnd_6376939 := by
    simpa [prefixWord, tailWord_6376939, baseEnd_6376939] using wordTrace_append hprefix tailTrace_6376939
  have hstable : (prefixWord ++ tailWord_6376939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376939).length < 2 ^ (prefixWord ++ tailWord_6376939).sum := by decide
  have hdescent : baseEnd_6376939 < baseStart_6376939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376969 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 8]
def baseStart_6376969 : Nat := 118140960795 + 6376969 * 2 ^ 59
def prefixEnd_6376969 : Nat := 4983230072969 + 3 ^ 40 * 6376969 * 2
def baseEnd_6376969 : Nat := 3274450215821365813160359

theorem tailTrace_6376969 : CollatzResearch.WordTrace tailWord_6376969 prefixEnd_6376969 3274450215821365813160359 := by
  unfold tailWord_6376969
  simp only [CollatzResearch.WordTrace]
  refine ⟨232587167234337887442661961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155058111489558591628441307 232587167234337887442661961)
  ·
    refine ⟨174440375425753415581996471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232587167234337887442661961 174440375425753415581996471)
    ·
      refine ⟨261660563138630123372994707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174440375425753415581996471 261660563138630123372994707)
      ·
        refine ⟨392490844707945185059492061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261660563138630123372994707 392490844707945185059492061)
        ·
          refine ⟨147184066765479444397309523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392490844707945185059492061 147184066765479444397309523)
          ·
            refine ⟨220776100148219166595964285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147184066765479444397309523 220776100148219166595964285)
            ·
              refine ⟨82791037555582187473486607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220776100148219166595964285 82791037555582187473486607)
              ·
                refine ⟨124186556333373281210229911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82791037555582187473486607 124186556333373281210229911)
                ·
                  refine ⟨186279834500059921815344867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124186556333373281210229911 186279834500059921815344867)
                  ·
                    refine ⟨279419751750089882723017301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 186279834500059921815344867 279419751750089882723017301)
                    ·
                      refine ⟨3274450215821365813160359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 279419751750089882723017301 3274450215821365813160359)
                      ·
                        rfl

theorem cell23_6376969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_6376969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376969 prefixEnd_6376969 := by exact prefixLift 6376969
  have htrace : WordTrace (prefixWord ++ tailWord_6376969) baseStart_6376969 baseEnd_6376969 := by
    simpa [prefixWord, tailWord_6376969, baseEnd_6376969] using wordTrace_append hprefix tailTrace_6376969
  have hstable : (prefixWord ++ tailWord_6376969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376969).length < 2 ^ (prefixWord ++ tailWord_6376969).sum := by decide
  have hdescent : baseEnd_6376969 < baseStart_6376969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376970 : List Nat := [3, 1, 2, 2, 2, 2, 2, 4, 1, 4]
def baseStart_6376970 : Nat := 118140960795 + 6376970 * 2 ^ 59
def prefixEnd_6376970 : Nat := 4983230072969 + 3 ^ 40 * 6376970 * 2
def baseEnd_6376970 : Nat := 1091483576434006769749285

theorem tailTrace_6376970 : CollatzResearch.WordTrace tailWord_6376970 prefixEnd_6376970 1091483576434006769749285 := by
  unfold tailWord_6376970
  simp only [CollatzResearch.WordTrace]
  refine ⟨58146800926833566153362091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155058135804889509742298909 58146800926833566153362091)
  ·
    refine ⟨87220201390250349230043137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58146800926833566153362091 87220201390250349230043137)
    ·
      refine ⟨65415151042687761922532353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87220201390250349230043137 65415151042687761922532353)
      ·
        refine ⟨49061363282015821441899265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65415151042687761922532353 49061363282015821441899265)
        ·
          refine ⟨36796022461511866081424449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49061363282015821441899265 36796022461511866081424449)
          ·
            refine ⟨27597016846133899561068337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36796022461511866081424449 27597016846133899561068337)
            ·
              refine ⟨20697762634600424670801253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27597016846133899561068337 20697762634600424670801253)
              ·
                refine ⟨3880830493987579625775235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20697762634600424670801253 3880830493987579625775235)
                ·
                  refine ⟨5821245740981369438662853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3880830493987579625775235 5821245740981369438662853)
                  ·
                    refine ⟨1091483576434006769749285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5821245740981369438662853 1091483576434006769749285)
                    ·
                      rfl

theorem cell23_6376970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_6376970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376970 prefixEnd_6376970 := by exact prefixLift 6376970
  have htrace : WordTrace (prefixWord ++ tailWord_6376970) baseStart_6376970 baseEnd_6376970 := by
    simpa [prefixWord, tailWord_6376970, baseEnd_6376970] using wordTrace_append hprefix tailTrace_6376970
  have hstable : (prefixWord ++ tailWord_6376970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376970).length < 2 ^ (prefixWord ++ tailWord_6376970).sum := by decide
  have hdescent : baseEnd_6376970 < baseStart_6376970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377013 : List Nat := [1, 3, 3, 1, 1, 3, 2, 3, 1, 5]
def baseStart_6377013 : Nat := 118140960795 + 6377013 * 2 ^ 59
def prefixEnd_6377013 : Nat := 4983230072969 + 3 ^ 40 * 6377013 * 2
def baseEnd_6377013 : Nat := 1091490936323387880336719

theorem tailTrace_6377013 : CollatzResearch.WordTrace tailWord_6377013 prefixEnd_6377013 1091490936323387880336719 := by
  unfold tailWord_6377013
  simp only [CollatzResearch.WordTrace]
  refine ⟨232588772046178482957263693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155059181364118988638175795 232588772046178482957263693)
  ·
    refine ⟨87220789517316931108973885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232588772046178482957263693 87220789517316931108973885)
    ·
      refine ⟨32707796068993849165865207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87220789517316931108973885 32707796068993849165865207)
      ·
        refine ⟨49061694103490773748797811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32707796068993849165865207 49061694103490773748797811)
        ·
          refine ⟨73592541155236160623196717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49061694103490773748797811 73592541155236160623196717)
          ·
            refine ⟨27597202933213560233698769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73592541155236160623196717 27597202933213560233698769)
            ·
              refine ⟨20697902199910170175274077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27597202933213560233698769 20697902199910170175274077)
              ·
                refine ⟨7761713324966313815727779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20697902199910170175274077 7761713324966313815727779)
                ·
                  refine ⟨11642569987449470723591669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7761713324966313815727779 11642569987449470723591669)
                  ·
                    refine ⟨1091490936323387880336719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11642569987449470723591669 1091490936323387880336719)
                    ·
                      rfl

theorem cell23_6377013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_6377013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377013 prefixEnd_6377013 := by exact prefixLift 6377013
  have htrace : WordTrace (prefixWord ++ tailWord_6377013) baseStart_6377013 baseEnd_6377013 := by
    simpa [prefixWord, tailWord_6377013, baseEnd_6377013] using wordTrace_append hprefix tailTrace_6377013
  have hstable : (prefixWord ++ tailWord_6377013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377013).length < 2 ^ (prefixWord ++ tailWord_6377013).sum := by decide
  have hdescent : baseEnd_6377013 < baseStart_6377013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377050 : List Nat := [3, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2]
def baseStart_6377050 : Nat := 118140960795 + 6377050 * 2 ^ 59
def prefixEnd_6377050 : Nat := 4983230072969 + 3 ^ 40 * 6377050 * 2
def baseEnd_6377050 : Nat := 3274491807754379996247487

theorem tailTrace_6377050 : CollatzResearch.WordTrace tailWord_6377050 prefixEnd_6377050 3274491807754379996247487 := by
  unfold tailWord_6377050
  simp only [CollatzResearch.WordTrace]
  refine ⟨58147530386761109569090151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155060081031362958850907069 58147530386761109569090151)
  ·
    refine ⟨87221295580141664353635227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58147530386761109569090151 87221295580141664353635227)
    ·
      refine ⟨130831943370212496530452841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87221295580141664353635227 130831943370212496530452841)
      ·
        refine ⟨98123957527659372397839631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130831943370212496530452841 98123957527659372397839631)
        ·
          refine ⟨147185936291489058596759447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98123957527659372397839631 147185936291489058596759447)
          ·
            refine ⟨220778904437233587895139171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147185936291489058596759447 220778904437233587895139171)
            ·
              refine ⟨331168356655850381842708757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220778904437233587895139171 331168356655850381842708757)
              ·
                refine ⟨15523516718242986648876973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 331168356655850381842708757 15523516718242986648876973)
                ·
                  refine ⟨5821318769341119993328865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15523516718242986648876973 5821318769341119993328865)
                  ·
                    refine ⟨4365989077005839994996649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5821318769341119993328865 4365989077005839994996649)
                    ·
                      refine ⟨3274491807754379996247487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4365989077005839994996649 3274491807754379996247487)
                      ·
                        rfl

theorem cell23_6377050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_6377050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377050 prefixEnd_6377050 := by exact prefixLift 6377050
  have htrace : WordTrace (prefixWord ++ tailWord_6377050) baseStart_6377050 baseEnd_6377050 := by
    simpa [prefixWord, tailWord_6377050, baseEnd_6377050] using wordTrace_append hprefix tailTrace_6377050
  have hstable : (prefixWord ++ tailWord_6377050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377050).length < 2 ^ (prefixWord ++ tailWord_6377050).sum := by decide
  have hdescent : baseEnd_6377050 < baseStart_6377050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377077 : List Nat := [1, 3, 4, 2, 1, 2, 2, 2, 2, 4]
def baseStart_6377077 : Nat := 118140960795 + 6377077 * 2 ^ 59
def prefixEnd_6377077 : Nat := 4983230072969 + 3 ^ 40 * 6377077 * 2
def baseEnd_6377077 : Nat := 1091501890577350463536621

theorem tailTrace_6377077 : CollatzResearch.WordTrace tailWord_6377077 prefixEnd_6377077 1091501890577350463536621 := by
  unfold tailWord_6377077
  simp only [CollatzResearch.WordTrace]
  refine ⟨232591106317946621887593485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155060737545297747925062323 232591106317946621887593485)
  ·
    refine ⟨87221664869229983207847557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232591106317946621887593485 87221664869229983207847557)
    ·
      refine ⟨16354062162980621851471417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87221664869229983207847557 16354062162980621851471417)
      ·
        refine ⟨12265546622235466388603563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16354062162980621851471417 12265546622235466388603563)
        ·
          refine ⟨18398319933353199582905345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12265546622235466388603563 18398319933353199582905345)
          ·
            refine ⟨13798739950014899687179009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18398319933353199582905345 13798739950014899687179009)
            ·
              refine ⟨10349054962511174765384257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13798739950014899687179009 10349054962511174765384257)
              ·
                refine ⟨7761791221883381074038193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10349054962511174765384257 7761791221883381074038193)
                ·
                  refine ⟨5821343416412535805528645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7761791221883381074038193 5821343416412535805528645)
                  ·
                    refine ⟨1091501890577350463536621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5821343416412535805528645 1091501890577350463536621)
                    ·
                      rfl

theorem cell23_6377077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_6377077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377077 prefixEnd_6377077 := by exact prefixLift 6377077
  have htrace : WordTrace (prefixWord ++ tailWord_6377077) baseStart_6377077 baseEnd_6377077 := by
    simpa [prefixWord, tailWord_6377077, baseEnd_6377077] using wordTrace_append hprefix tailTrace_6377077
  have hstable : (prefixWord ++ tailWord_6377077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377077).length < 2 ^ (prefixWord ++ tailWord_6377077).sum := by decide
  have hdescent : baseEnd_6377077 < baseStart_6377077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377100 : List Nat := [2, 2, 1, 2, 1, 1, 3, 5, 2, 1, 3]
def baseStart_6377100 : Nat := 118140960795 + 6377100 * 2 ^ 59
def prefixEnd_6377100 : Nat := 4983230072969 + 3 ^ 40 * 6377100 * 2
def baseEnd_6377100 : Nat := 3274517481787104800622257

theorem tailTrace_6377100 : CollatzResearch.WordTrace tailWord_6377100 prefixEnd_6377100 3274517481787104800622257 := by
  unfold tailWord_6377100
  simp only [CollatzResearch.WordTrace]
  refine ⟨116295972598431648407840377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155061296797908864543787169 116295972598431648407840377)
  ·
    refine ⟨87221979448823736305880283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116295972598431648407840377 87221979448823736305880283)
    ·
      refine ⟨130832969173235604458820425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87221979448823736305880283 130832969173235604458820425)
      ·
        refine ⟨98124726879926703344115319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130832969173235604458820425 98124726879926703344115319)
        ·
          refine ⟨147187090319890055016172979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98124726879926703344115319 147187090319890055016172979)
          ·
            refine ⟨220780635479835082524259469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147187090319890055016172979 220780635479835082524259469)
            ·
              refine ⟨82792738304938155946597301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220780635479835082524259469 82792738304938155946597301)
              ·
                refine ⟨7761819216087952119993497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82792738304938155946597301 7761819216087952119993497)
                ·
                  refine ⟨5821364412065964089995123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7761819216087952119993497 5821364412065964089995123)
                  ·
                    refine ⟨8732046618098946134992685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5821364412065964089995123 8732046618098946134992685)
                    ·
                      refine ⟨3274517481787104800622257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8732046618098946134992685 3274517481787104800622257)
                      ·
                        rfl

theorem cell23_6377100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_6377100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377100 prefixEnd_6377100 := by exact prefixLift 6377100
  have htrace : WordTrace (prefixWord ++ tailWord_6377100) baseStart_6377100 baseEnd_6377100 := by
    simpa [prefixWord, tailWord_6377100, baseEnd_6377100] using wordTrace_append hprefix tailTrace_6377100
  have hstable : (prefixWord ++ tailWord_6377100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377100).length < 2 ^ (prefixWord ++ tailWord_6377100).sum := by decide
  have hdescent : baseEnd_6377100 < baseStart_6377100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377128 : List Nat := [2, 1, 7, 1, 2, 1, 1, 2, 2, 4]
def baseStart_6377128 : Nat := 118140960795 + 6377128 * 2 ^ 59
def prefixEnd_6377128 : Nat := 4983230072969 + 3 ^ 40 * 6377128 * 2
def baseEnd_6377128 : Nat := 1091510619748476897024043

theorem tailTrace_6377128 : CollatzResearch.WordTrace tailWord_6377128 prefixEnd_6377128 1091510619748476897024043 := by
  unfold tailWord_6377128
  simp only [CollatzResearch.WordTrace]
  refine ⟨116296483220380928798850019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155061977627174571731800025 116296483220380928798850019)
  ·
    refine ⟨174444724830571393198275029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116296483220380928798850019 174444724830571393198275029)
    ·
      refine ⟨4088548238216517028084571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 174444724830571393198275029 4088548238216517028084571)
      ·
        refine ⟨6132822357324775542126857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4088548238216517028084571 6132822357324775542126857)
        ·
          refine ⟨4599616767993581656595143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6132822357324775542126857 4599616767993581656595143)
          ·
            refine ⟨6899425151990372484892715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4599616767993581656595143 6899425151990372484892715)
            ·
              refine ⟨10349137727985558727339073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6899425151990372484892715 10349137727985558727339073)
              ·
                refine ⟨7761853295989169045504305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10349137727985558727339073 7761853295989169045504305)
                ·
                  refine ⟨5821389971991876784128229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7761853295989169045504305 5821389971991876784128229)
                  ·
                    refine ⟨1091510619748476897024043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5821389971991876784128229 1091510619748476897024043)
                    ·
                      rfl

theorem cell23_6377128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_6377128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377128 prefixEnd_6377128 := by exact prefixLift 6377128
  have htrace : WordTrace (prefixWord ++ tailWord_6377128) baseStart_6377128 baseEnd_6377128 := by
    simpa [prefixWord, tailWord_6377128, baseEnd_6377128] using wordTrace_append hprefix tailTrace_6377128
  have hstable : (prefixWord ++ tailWord_6377128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377128).length < 2 ^ (prefixWord ++ tailWord_6377128).sum := by decide
  have hdescent : baseEnd_6377128 < baseStart_6377128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377133 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_6377133 : Nat := 118140960795 + 6377133 * 2 ^ 59
def prefixEnd_6377133 : Nat := 4983230072969 + 3 ^ 40 * 6377133 * 2
def baseEnd_6377133 : Nat := 1091511475549567723836535

theorem tailTrace_6377133 : CollatzResearch.WordTrace tailWord_6377133 prefixEnd_6377133 1091511475549567723836535 := by
  unfold tailWord_6377133
  simp only [CollatzResearch.WordTrace]
  refine ⟨232593148805743743451632053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155062099203829162301088035 232593148805743743451632053)
  ·
    refine ⟨21805607700538475948590505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232593148805743743451632053 21805607700538475948590505)
    ·
      refine ⟨16354205775403856961442879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21805607700538475948590505 16354205775403856961442879)
      ·
        refine ⟨24531308663105785442164319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16354205775403856961442879 24531308663105785442164319)
        ·
          refine ⟨36796962994658678163246479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24531308663105785442164319 36796962994658678163246479)
          ·
            refine ⟨55195444491988017244869719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36796962994658678163246479 55195444491988017244869719)
            ·
              refine ⟨82793166737982025867304579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55195444491988017244869719 82793166737982025867304579)
              ·
                refine ⟨124189750106973038800956869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82793166737982025867304579 124189750106973038800956869)
                ·
                  refine ⟨23285578145057444775179413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124189750106973038800956869 23285578145057444775179413)
                  ·
                    refine ⟨1091511475549567723836535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23285578145057444775179413 1091511475549567723836535)
                    ·
                      rfl

theorem cell23_6377133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_6377133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377133 prefixEnd_6377133 := by exact prefixLift 6377133
  have htrace : WordTrace (prefixWord ++ tailWord_6377133) baseStart_6377133 baseEnd_6377133 := by
    simpa [prefixWord, tailWord_6377133, baseEnd_6377133] using wordTrace_append hprefix tailTrace_6377133
  have hstable : (prefixWord ++ tailWord_6377133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377133).length < 2 ^ (prefixWord ++ tailWord_6377133).sum := by decide
  have hdescent : baseEnd_6377133 < baseStart_6377133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377134 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_6377134 : Nat := 118140960795 + 6377134 * 2 ^ 59
def prefixEnd_6377134 : Nat := 4983230072969 + 3 ^ 40 * 6377134 * 2
def baseEnd_6377134 : Nat := 3274534940129357667597101

theorem tailTrace_6377134 : CollatzResearch.WordTrace tailWord_6377134 prefixEnd_6377134 3274534940129357667597101 := by
  unfold tailWord_6377134
  simp only [CollatzResearch.WordTrace]
  refine ⟨29074148159842515077802307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155062123519160080414945637 29074148159842515077802307)
  ·
    refine ⟨43611222239763772616703461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29074148159842515077802307 43611222239763772616703461)
    ·
      refine ⟨8177104169955707365631899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43611222239763772616703461 8177104169955707365631899)
      ·
        refine ⟨12265656254933561048447849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8177104169955707365631899 12265656254933561048447849)
        ·
          refine ⟨9199242191200170786335887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12265656254933561048447849 9199242191200170786335887)
          ·
            refine ⟨13798863286800256179503831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9199242191200170786335887 13798863286800256179503831)
            ·
              refine ⟨20698294930200384269255747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13798863286800256179503831 20698294930200384269255747)
              ·
                refine ⟨31047442395300576403883621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20698294930200384269255747 31047442395300576403883621)
                ·
                  refine ⟨5821395449118858075728179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31047442395300576403883621 5821395449118858075728179)
                  ·
                    refine ⟨8732093173678287113592269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5821395449118858075728179 8732093173678287113592269)
                    ·
                      refine ⟨3274534940129357667597101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8732093173678287113592269 3274534940129357667597101)
                      ·
                        rfl

theorem cell23_6377134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_6377134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377134 prefixEnd_6377134 := by exact prefixLift 6377134
  have htrace : WordTrace (prefixWord ++ tailWord_6377134) baseStart_6377134 baseEnd_6377134 := by
    simpa [prefixWord, tailWord_6377134, baseEnd_6377134] using wordTrace_append hprefix tailTrace_6377134
  have hstable : (prefixWord ++ tailWord_6377134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377134).length < 2 ^ (prefixWord ++ tailWord_6377134).sum := by decide
  have hdescent : baseEnd_6377134 < baseStart_6377134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377213 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_6377213 : Nat := 118140960795 + 6377213 * 2 ^ 59
def prefixEnd_6377213 : Nat := 4983230072969 + 3 ^ 40 * 6377213 * 2
def baseEnd_6377213 : Nat := 3274575505101062858509237

theorem tailTrace_6377213 : CollatzResearch.WordTrace tailWord_6377213 prefixEnd_6377213 3274575505101062858509237 := by
  unfold tailWord_6377213
  simp only [CollatzResearch.WordTrace]
  refine ⟨232596066645453917114544293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155064044430302611409696195 232596066645453917114544293)
  ·
    refine ⟨43611762496022609458977055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232596066645453917114544293 43611762496022609458977055)
    ·
      refine ⟨65417643744033914188465583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43611762496022609458977055 65417643744033914188465583)
      ·
        refine ⟨98126465616050871282698375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65417643744033914188465583 98126465616050871282698375)
        ·
          refine ⟨147189698424076306924047563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98126465616050871282698375 147189698424076306924047563)
          ·
            refine ⟨220784547636114460386071345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147189698424076306924047563 220784547636114460386071345)
            ·
              refine ⟨165588410727085845289553509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220784547636114460386071345 165588410727085845289553509)
              ·
                refine ⟨31047827011328595991791283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165588410727085845289553509 31047827011328595991791283)
                ·
                  refine ⟨46571740516992893987686925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31047827011328595991791283 46571740516992893987686925)
                  ·
                    refine ⟨17464402693872335245382597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46571740516992893987686925 17464402693872335245382597)
                    ·
                      refine ⟨3274575505101062858509237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17464402693872335245382597 3274575505101062858509237)
                      ·
                        rfl

theorem cell23_6377213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_6377213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377213 prefixEnd_6377213 := by exact prefixLift 6377213
  have htrace : WordTrace (prefixWord ++ tailWord_6377213) baseStart_6377213 baseEnd_6377213 := by
    simpa [prefixWord, tailWord_6377213, baseEnd_6377213] using wordTrace_append hprefix tailTrace_6377213
  have hstable : (prefixWord ++ tailWord_6377213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377213).length < 2 ^ (prefixWord ++ tailWord_6377213).sum := by decide
  have hdescent : baseEnd_6377213 < baseStart_6377213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377230 : List Nat := [4, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4]
def baseStart_6377230 : Nat := 118140960795 + 6377230 * 2 ^ 59
def prefixEnd_6377230 : Nat := 4983230072969 + 3 ^ 40 * 6377230 * 2
def baseEnd_6377230 : Nat := 3274584234272189291996659

theorem tailTrace_6377230 : CollatzResearch.WordTrace tailWord_6377230 prefixEnd_6377230 3274584234272189291996659 := by
  unfold tailWord_6377230
  simp only [CollatzResearch.WordTrace]
  refine ⟨29074585835799041127239143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155064457790928219345275429 29074585835799041127239143)
  ·
    refine ⟨43611878753698561690858715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29074585835799041127239143 43611878753698561690858715)
    ·
      refine ⟨65417818130547842536288073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43611878753698561690858715 65417818130547842536288073)
      ·
        refine ⟨49063363597910881902216055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65417818130547842536288073 49063363597910881902216055)
        ·
          refine ⟨73595045396866322853324083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49063363597910881902216055 73595045396866322853324083)
          ·
            refine ⟨110392568095299484279986125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73595045396866322853324083 110392568095299484279986125)
            ·
              refine ⟨41397213035737306604994797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110392568095299484279986125 41397213035737306604994797)
              ·
                refine ⟨15523954888401489976873049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41397213035737306604994797 15523954888401489976873049)
                ·
                  refine ⟨11642966166301117482654787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15523954888401489976873049 11642966166301117482654787)
                  ·
                    refine ⟨17464449249451676223982181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11642966166301117482654787 17464449249451676223982181)
                    ·
                      refine ⟨3274584234272189291996659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17464449249451676223982181 3274584234272189291996659)
                      ·
                        rfl

theorem cell23_6377230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_6377230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377230 prefixEnd_6377230 := by exact prefixLift 6377230
  have htrace : WordTrace (prefixWord ++ tailWord_6377230) baseStart_6377230 baseEnd_6377230 := by
    simpa [prefixWord, tailWord_6377230, baseEnd_6377230] using wordTrace_append hprefix tailTrace_6377230
  have hstable : (prefixWord ++ tailWord_6377230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377230).length < 2 ^ (prefixWord ++ tailWord_6377230).sum := by decide
  have hdescent : baseEnd_6377230 < baseStart_6377230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377314 : List Nat := [3, 3, 2, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_6377314 : Nat := 118140960795 + 6377314 * 2 ^ 59
def prefixEnd_6377314 : Nat := 4983230072969 + 3 ^ 40 * 6377314 * 2
def baseEnd_6377314 : Nat := 3274627366647166963346273

theorem tailTrace_6377314 : CollatzResearch.WordTrace tailWord_6377314 prefixEnd_6377314 3274627366647166963346273 := by
  unfold tailWord_6377314
  simp only [CollatzResearch.WordTrace]
  refine ⟨58149937604522002840992749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155066500278725340909313997 58149937604522002840992749)
  ·
    refine ⟨21806226601695751065372281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58149937604522002840992749 21806226601695751065372281)
    ·
      refine ⟨16354669951271813299029211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21806226601695751065372281 16354669951271813299029211)
      ·
        refine ⟨24532004926907719948543817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16354669951271813299029211 24532004926907719948543817)
        ·
          refine ⟨18399003695180789961407863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24532004926907719948543817 18399003695180789961407863)
          ·
            refine ⟨27598505542771184942111795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18399003695180789961407863 27598505542771184942111795)
            ·
              refine ⟨41397758314156777413167693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27598505542771184942111795 41397758314156777413167693)
              ·
                refine ⟨15524159367808791529937885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41397758314156777413167693 15524159367808791529937885)
                ·
                  refine ⟨5821559762928296823726707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15524159367808791529937885 5821559762928296823726707)
                  ·
                    refine ⟨8732339644392445235590061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5821559762928296823726707 8732339644392445235590061)
                    ·
                      refine ⟨3274627366647166963346273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8732339644392445235590061 3274627366647166963346273)
                      ·
                        rfl

theorem cell23_6377314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_6377314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377314 prefixEnd_6377314 := by exact prefixLift 6377314
  have htrace : WordTrace (prefixWord ++ tailWord_6377314) baseStart_6377314 baseEnd_6377314 := by
    simpa [prefixWord, tailWord_6377314, baseEnd_6377314] using wordTrace_append hprefix tailTrace_6377314
  have hstable : (prefixWord ++ tailWord_6377314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377314).length < 2 ^ (prefixWord ++ tailWord_6377314).sum := by decide
  have hdescent : baseEnd_6377314 < baseStart_6377314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377337 : List Nat := [1, 2, 1, 3, 2, 2, 4, 2, 1, 1, 4]
def baseStart_6377337 : Nat := 118140960795 + 6377337 * 2 ^ 59
def prefixEnd_6377337 : Nat := 4983230072969 + 3 ^ 40 * 6377337 * 2
def baseEnd_6377337 : Nat := 3274639176702220373358667

theorem tailTrace_6377337 : CollatzResearch.WordTrace tailWord_6377337 prefixEnd_6377337 3274639176702220373358667 := by
  unfold tailWord_6377337
  simp only [CollatzResearch.WordTrace]
  refine ⟨232600589297004686292058265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155067059531336457528038843 232600589297004686292058265)
  ·
    refine ⟨174450441972753514719043699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232600589297004686292058265 174450441972753514719043699)
    ·
      refine ⟨261675662959130272078565549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174450441972753514719043699 261675662959130272078565549)
      ·
        refine ⟨98128373609673852029462081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261675662959130272078565549 98128373609673852029462081)
        ·
          refine ⟨73596280207255389022096561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98128373609673852029462081 73596280207255389022096561)
          ·
            refine ⟨55197210155441541766572421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73596280207255389022096561 55197210155441541766572421)
            ·
              refine ⟨10349476904145289081232329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55197210155441541766572421 10349476904145289081232329)
              ·
                refine ⟨7762107678108966810924247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10349476904145289081232329 7762107678108966810924247)
                ·
                  refine ⟨11643161517163450216386371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7762107678108966810924247 11643161517163450216386371)
                  ·
                    refine ⟨17464742275745175324579557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11643161517163450216386371 17464742275745175324579557)
                    ·
                      refine ⟨3274639176702220373358667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17464742275745175324579557 3274639176702220373358667)
                      ·
                        rfl

theorem cell23_6377337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_6377337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377337 prefixEnd_6377337 := by exact prefixLift 6377337
  have htrace : WordTrace (prefixWord ++ tailWord_6377337) baseStart_6377337 baseEnd_6377337 := by
    simpa [prefixWord, tailWord_6377337, baseEnd_6377337] using wordTrace_append hprefix tailTrace_6377337
  have hstable : (prefixWord ++ tailWord_6377337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377337).length < 2 ^ (prefixWord ++ tailWord_6377337).sum := by decide
  have hdescent : baseEnd_6377337 < baseStart_6377337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377377 : List Nat := [1, 2, 3, 4, 2, 1, 2, 8]
def baseStart_6377377 : Nat := 118140960795 + 6377377 * 2 ^ 59
def prefixEnd_6377377 : Nat := 4983230072969 + 3 ^ 40 * 6377377 * 2
def baseEnd_6377377 : Nat := 121283693182533341365129

theorem tailTrace_6377377 : CollatzResearch.WordTrace tailWord_6377377 prefixEnd_6377377 121283693182533341365129 := by
  unfold tailWord_6377377
  simp only [CollatzResearch.WordTrace]
  refine ⟨232602048216859773123514385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155068032144573182082342923 232602048216859773123514385)
  ·
    refine ⟨174451536162644829842635789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232602048216859773123514385 174451536162644829842635789)
    ·
      refine ⟨65419326060991811190988421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174451536162644829842635789 65419326060991811190988421)
      ·
        refine ⟨12266123636435964598310329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65419326060991811190988421 12266123636435964598310329)
        ·
          refine ⟨9199592727326973448732747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12266123636435964598310329 9199592727326973448732747)
          ·
            refine ⟨13799389090990460173099121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9199592727326973448732747 13799389090990460173099121)
            ·
              refine ⟨10349541818242845129824341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13799389090990460173099121 10349541818242845129824341)
              ·
                refine ⟨121283693182533341365129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10349541818242845129824341 121283693182533341365129)
                ·
                  rfl

theorem cell23_6377377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 8].length) (baseStart_6377377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377377 prefixEnd_6377377 := by exact prefixLift 6377377
  have htrace : WordTrace (prefixWord ++ tailWord_6377377) baseStart_6377377 baseEnd_6377377 := by
    simpa [prefixWord, tailWord_6377377, baseEnd_6377377] using wordTrace_append hprefix tailTrace_6377377
  have hstable : (prefixWord ++ tailWord_6377377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377377).length < 2 ^ (prefixWord ++ tailWord_6377377).sum := by decide
  have hdescent : baseEnd_6377377 < baseStart_6377377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377444 : List Nat := [2, 3, 1, 1, 1, 1, 6, 1, 1, 4, 2]
def baseStart_6377444 : Nat := 118140960795 + 6377444 * 2 ^ 59
def prefixEnd_6377444 : Nat := 4983230072969 + 3 ^ 40 * 6377444 * 2
def baseEnd_6377444 : Nat := 3274694119132251454720675

theorem tailTrace_6377444 : CollatzResearch.WordTrace tailWord_6377444 prefixEnd_6377444 3274694119132251454720675 := by
  unfold tailWord_6377444
  simp only [CollatzResearch.WordTrace]
  refine ⟨116302245953808521783101693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155069661271744695710802257 116302245953808521783101693)
  ·
    refine ⟨43613342232678195668663135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116302245953808521783101693 43613342232678195668663135)
    ·
      refine ⟨65420013349017293502994703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43613342232678195668663135 65420013349017293502994703)
      ·
        refine ⟨98130020023525940254492055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65420013349017293502994703 98130020023525940254492055)
        ·
          refine ⟨147195030035288910381738083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98130020023525940254492055 147195030035288910381738083)
          ·
            refine ⟨220792545052933365572607125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147195030035288910381738083 220792545052933365572607125)
            ·
              refine ⟨10349650549356251511215959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 220792545052933365572607125 10349650549356251511215959)
              ·
                refine ⟨15524475824034377266823939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10349650549356251511215959 15524475824034377266823939)
                ·
                  refine ⟨23286713736051565900235909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15524475824034377266823939 23286713736051565900235909)
                  ·
                    refine ⟨4366258825509668606294233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23286713736051565900235909 4366258825509668606294233)
                    ·
                      refine ⟨3274694119132251454720675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4366258825509668606294233 3274694119132251454720675)
                      ·
                        rfl

theorem cell23_6377444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_6377444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377444 prefixEnd_6377444 := by exact prefixLift 6377444
  have htrace : WordTrace (prefixWord ++ tailWord_6377444) baseStart_6377444 baseEnd_6377444 := by
    simpa [prefixWord, tailWord_6377444, baseEnd_6377444] using wordTrace_append hprefix tailTrace_6377444
  have hstable : (prefixWord ++ tailWord_6377444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377444).length < 2 ^ (prefixWord ++ tailWord_6377444).sum := by decide
  have hdescent : baseEnd_6377444 < baseStart_6377444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377467 : List Nat := [1, 1, 1, 1, 1, 3, 5, 5, 5]
def baseStart_6377467 : Nat := 118140960795 + 6377467 * 2 ^ 59
def prefixEnd_6377467 : Nat := 4983230072969 + 3 ^ 40 * 6377467 * 2
def baseEnd_6377467 : Nat := 363856214354144984970341

theorem tailTrace_6377467 : CollatzResearch.WordTrace tailWord_6377467 prefixEnd_6377467 363856214354144984970341 := by
  unfold tailWord_6377467
  simp only [CollatzResearch.WordTrace]
  refine ⟨232605330786533718494290655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155070220524355812329527103 232605330786533718494290655)
  ·
    refine ⟨348907996179800577741435983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232605330786533718494290655 348907996179800577741435983)
    ·
      refine ⟨523361994269700866612153975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348907996179800577741435983 523361994269700866612153975)
      ·
        refine ⟨785042991404551299918230963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523361994269700866612153975 785042991404551299918230963)
        ·
          refine ⟨1177564487106826949877346445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785042991404551299918230963 1177564487106826949877346445)
          ·
            refine ⟨441586682665060106204004917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1177564487106826949877346445 441586682665060106204004917)
            ·
              refine ⟨41398751499849384956625461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 441586682665060106204004917 41398751499849384956625461)
              ·
                refine ⟨3881132953110879839683637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41398751499849384956625461 3881132953110879839683637)
                ·
                  refine ⟨363856214354144984970341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3881132953110879839683637 363856214354144984970341)
                  ·
                    rfl

theorem cell23_6377467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 5].length) (baseStart_6377467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377467 prefixEnd_6377467 := by exact prefixLift 6377467
  have htrace : WordTrace (prefixWord ++ tailWord_6377467) baseStart_6377467 baseEnd_6377467 := by
    simpa [prefixWord, tailWord_6377467, baseEnd_6377467] using wordTrace_append hprefix tailTrace_6377467
  have hstable : (prefixWord ++ tailWord_6377467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377467).length < 2 ^ (prefixWord ++ tailWord_6377467).sum := by decide
  have hdescent : baseEnd_6377467 < baseStart_6377467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377477 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 2, 3, 3]
def baseStart_6377477 : Nat := 118140960795 + 6377477 * 2 ^ 59
def prefixEnd_6377477 : Nat := 4983230072969 + 3 ^ 40 * 6377477 * 2
def baseEnd_6377477 : Nat := 3274711063993849825608023

theorem tailTrace_6377477 : CollatzResearch.WordTrace tailWord_6377477 prefixEnd_6377477 3274711063993849825608023 := by
  unfold tailWord_6377477
  simp only [CollatzResearch.WordTrace]
  refine ⟨232605695516497490202154685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155070463677664993468103123 232605695516497490202154685)
  ·
    refine ⟨87227135818686558825808007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232605695516497490202154685 87227135818686558825808007)
    ·
      refine ⟨130840703728029838238712011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87227135818686558825808007 130840703728029838238712011)
      ·
        refine ⟨196261055592044757358068017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130840703728029838238712011 196261055592044757358068017)
        ·
          refine ⟨147195791694033568018551013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196261055592044757358068017 147195791694033568018551013)
          ·
            refine ⟨27599210942631294003478315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147195791694033568018551013 27599210942631294003478315)
            ·
              refine ⟨41398816413946941005217473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27599210942631294003478315 41398816413946941005217473)
              ·
                refine ⟨31049112310460205753913105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41398816413946941005217473 31049112310460205753913105)
                ·
                  refine ⟨23286834232845154315434829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31049112310460205753913105 23286834232845154315434829)
                  ·
                    refine ⟨8732562837316932868288061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23286834232845154315434829 8732562837316932868288061)
                    ·
                      refine ⟨3274711063993849825608023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8732562837316932868288061 3274711063993849825608023)
                      ·
                        rfl

theorem cell23_6377477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_6377477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377477 prefixEnd_6377477 := by exact prefixLift 6377477
  have htrace : WordTrace (prefixWord ++ tailWord_6377477) baseStart_6377477 baseEnd_6377477 := by
    simpa [prefixWord, tailWord_6377477, baseEnd_6377477] using wordTrace_append hprefix tailTrace_6377477
  have hstable : (prefixWord ++ tailWord_6377477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377477).length < 2 ^ (prefixWord ++ tailWord_6377477).sum := by decide
  have hdescent : baseEnd_6377477 < baseStart_6377477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377495 : List Nat := [1, 1, 3, 5, 2, 1, 3, 1, 2, 2, 2]
def baseStart_6377495 : Nat := 118140960795 + 6377495 * 2 ^ 59
def prefixEnd_6377495 : Nat := 4983230072969 + 3 ^ 40 * 6377495 * 2
def baseEnd_6377495 : Nat := 3274720306645630755182941

theorem tailTrace_6377495 : CollatzResearch.WordTrace tailWord_6377495 prefixEnd_6377495 3274720306645630755182941 := by
  unfold tailWord_6377495
  simp only [CollatzResearch.WordTrace]
  refine ⟨232606352030432279276309939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155070901353621519517539959 232606352030432279276309939)
  ·
    refine ⟨348909528045648418914464909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232606352030432279276309939 348909528045648418914464909)
    ·
      refine ⟨130841073017118157092924341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348909528045648418914464909 130841073017118157092924341)
      ·
        refine ⟨12266350595354827227461657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130841073017118157092924341 12266350595354827227461657)
        ·
          refine ⟨9199762946516120420596243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12266350595354827227461657 9199762946516120420596243)
          ·
            refine ⟨13799644419774180630894365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9199762946516120420596243 13799644419774180630894365)
            ·
              refine ⟨5174866657415317736585387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13799644419774180630894365 5174866657415317736585387)
              ·
                refine ⟨7762299986122976604878081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5174866657415317736585387 7762299986122976604878081)
                ·
                  refine ⟨5821724989592232453658561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7762299986122976604878081 5821724989592232453658561)
                  ·
                    refine ⟨4366293742194174340243921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5821724989592232453658561 4366293742194174340243921)
                    ·
                      refine ⟨3274720306645630755182941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4366293742194174340243921 3274720306645630755182941)
                      ·
                        rfl

theorem cell23_6377495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_6377495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377495 prefixEnd_6377495 := by exact prefixLift 6377495
  have htrace : WordTrace (prefixWord ++ tailWord_6377495) baseStart_6377495 baseEnd_6377495 := by
    simpa [prefixWord, tailWord_6377495, baseEnd_6377495] using wordTrace_append hprefix tailTrace_6377495
  have hstable : (prefixWord ++ tailWord_6377495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377495).length < 2 ^ (prefixWord ++ tailWord_6377495).sum := by decide
  have hdescent : baseEnd_6377495 < baseStart_6377495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377527 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 5, 4]
def baseStart_6377527 : Nat := 118140960795 + 6377527 * 2 ^ 59
def prefixEnd_6377527 : Nat := 4983230072969 + 3 ^ 40 * 6377527 * 2
def baseEnd_6377527 : Nat := 1091578912675524876660931

theorem tailTrace_6377527 : CollatzResearch.WordTrace tailWord_6377527 prefixEnd_6377527 1091578912675524876660931 := by
  unfold tailWord_6377527
  simp only [CollatzResearch.WordTrace]
  refine ⟨232607519166316348741474835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155071679444210899160983223 232607519166316348741474835)
  ·
    refine ⟨348911278749474523112212253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232607519166316348741474835 348911278749474523112212253)
    ·
      refine ⟨130841729531052946167079595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348911278749474523112212253 130841729531052946167079595)
      ·
        refine ⟨196262594296579419250619393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130841729531052946167079595 196262594296579419250619393)
        ·
          refine ⟨147196945722434564437964545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196262594296579419250619393 147196945722434564437964545)
          ·
            refine ⟨110397709291825923328473409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147196945722434564437964545 110397709291825923328473409)
            ·
              refine ⟨82798281968869442496355057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110397709291825923328473409 82798281968869442496355057)
              ·
                refine ⟨62098711476652081872266293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82798281968869442496355057 62098711476652081872266293)
                ·
                  refine ⟨5821754200936132675524965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62098711476652081872266293 5821754200936132675524965)
                  ·
                    refine ⟨1091578912675524876660931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5821754200936132675524965 1091578912675524876660931)
                    ·
                      rfl

theorem cell23_6377527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 4].length) (baseStart_6377527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377527 prefixEnd_6377527 := by exact prefixLift 6377527
  have htrace : WordTrace (prefixWord ++ tailWord_6377527) baseStart_6377527 baseEnd_6377527 := by
    simpa [prefixWord, tailWord_6377527, baseEnd_6377527] using wordTrace_append hprefix tailTrace_6377527
  have hstable : (prefixWord ++ tailWord_6377527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377527).length < 2 ^ (prefixWord ++ tailWord_6377527).sum := by decide
  have hdescent : baseEnd_6377527 < baseStart_6377527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377622 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_6377622 : Nat := 118140960795 + 6377622 * 2 ^ 59
def prefixEnd_6377622 : Nat := 4983230072969 + 3 ^ 40 * 6377622 * 2
def baseEnd_6377622 : Nat := 3274785518688751758294857

theorem tailTrace_6377622 : CollatzResearch.WordTrace tailWord_6377622 prefixEnd_6377622 3274785518688751758294857 := by
  unfold tailWord_6377622
  simp only [CollatzResearch.WordTrace]
  refine ⟨14538186506310761247886445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155073989400648119977455413 14538186506310761247886445)
  ·
    refine ⟨5451819939866535467957417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14538186506310761247886445 5451819939866535467957417)
    ·
      refine ⟨4088864954899901600968063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5451819939866535467957417 4088864954899901600968063)
      ·
        refine ⟨6133297432349852401452095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4088864954899901600968063 6133297432349852401452095)
        ·
          refine ⟨9199946148524778602178143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6133297432349852401452095 9199946148524778602178143)
          ·
            refine ⟨13799919222787167903267215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9199946148524778602178143 13799919222787167903267215)
            ·
              refine ⟨20699878834180751854900823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13799919222787167903267215 20699878834180751854900823)
              ·
                refine ⟨31049818251271127782351235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20699878834180751854900823 31049818251271127782351235)
                ·
                  refine ⟨46574727376906691673526853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31049818251271127782351235 46574727376906691673526853)
                  ·
                    refine ⟨8732761383170004688786285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46574727376906691673526853 8732761383170004688786285)
                    ·
                      refine ⟨3274785518688751758294857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8732761383170004688786285 3274785518688751758294857)
                      ·
                        rfl

theorem cell23_6377622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_6377622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377622 prefixEnd_6377622 := by exact prefixLift 6377622
  have htrace : WordTrace (prefixWord ++ tailWord_6377622) baseStart_6377622 baseEnd_6377622 := by
    simpa [prefixWord, tailWord_6377622, baseEnd_6377622] using wordTrace_append hprefix tailTrace_6377622
  have hstable : (prefixWord ++ tailWord_6377622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377622).length < 2 ^ (prefixWord ++ tailWord_6377622).sum := by decide
  have hdescent : baseEnd_6377622 < baseStart_6377622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377627 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 3]
def baseStart_6377627 : Nat := 118140960795 + 6377627 * 2 ^ 59
def prefixEnd_6377627 : Nat := 4983230072969 + 3 ^ 40 * 6377627 * 2
def baseEnd_6377627 : Nat := 3274788086092024238732333

theorem tailTrace_6377627 : CollatzResearch.WordTrace tailWord_6377627 prefixEnd_6377627 3274788086092024238732333 := by
  unfold tailWord_6377627
  simp only [CollatzResearch.WordTrace]
  refine ⟨232611166465954065820115135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155074110977302710546743423 232611166465954065820115135)
  ·
    refine ⟨348916749698931098730172703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232611166465954065820115135 348916749698931098730172703)
    ·
      refine ⟨523375124548396648095259055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348916749698931098730172703 523375124548396648095259055)
      ·
        refine ⟨785062686822594972142888583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523375124548396648095259055 785062686822594972142888583)
        ·
          refine ⟨1177594030233892458214332875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785062686822594972142888583 1177594030233892458214332875)
          ·
            refine ⟨1766391045350838687321499313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177594030233892458214332875 1766391045350838687321499313)
            ·
              refine ⟨1324793284013129015491124485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1766391045350838687321499313 1324793284013129015491124485)
              ·
                refine ⟨248398740752461690404585841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1324793284013129015491124485 248398740752461690404585841)
                ·
                  refine ⟨186299055564346267803439381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248398740752461690404585841 186299055564346267803439381)
                  ·
                    refine ⟨8732768229578731303286221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 186299055564346267803439381 8732768229578731303286221)
                    ·
                      refine ⟨3274788086092024238732333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8732768229578731303286221 3274788086092024238732333)
                      ·
                        rfl

theorem cell23_6377627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 3].length) (baseStart_6377627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377627 prefixEnd_6377627 := by exact prefixLift 6377627
  have htrace : WordTrace (prefixWord ++ tailWord_6377627) baseStart_6377627 baseEnd_6377627 := by
    simpa [prefixWord, tailWord_6377627, baseEnd_6377627] using wordTrace_append hprefix tailTrace_6377627
  have hstable : (prefixWord ++ tailWord_6377627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377627).length < 2 ^ (prefixWord ++ tailWord_6377627).sum := by decide
  have hdescent : baseEnd_6377627 < baseStart_6377627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377678 : List Nat := [4, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3]
def baseStart_6377678 : Nat := 118140960795 + 6377678 * 2 ^ 59
def prefixEnd_6377678 : Nat := 4983230072969 + 3 ^ 40 * 6377678 * 2
def baseEnd_6377678 : Nat := 3274814273605403539194599

theorem tailTrace_6377678 : CollatzResearch.WordTrace tailWord_6377678 prefixEnd_6377678 3274814273605403539194599 := by
  unfold tailWord_6377678
  simp only [CollatzResearch.WordTrace]
  refine ⟨29076628323596162691277711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155075351059179534353481125 29076628323596162691277711)
  ·
    refine ⟨43614942485394244036916567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29076628323596162691277711 43614942485394244036916567)
    ·
      refine ⟨65422413728091366055374851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43614942485394244036916567 65422413728091366055374851)
      ·
        refine ⟨98133620592137049083062277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65422413728091366055374851 98133620592137049083062277)
        ·
          refine ⟨18400053861025696703074177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98133620592137049083062277 18400053861025696703074177)
          ·
            refine ⟨13800040395769272527305633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18400053861025696703074177 13800040395769272527305633)
            ·
              refine ⟨10350030296826954395479225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13800040395769272527305633 10350030296826954395479225)
              ·
                refine ⟨7762522722620215796609419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10350030296826954395479225 7762522722620215796609419)
                ·
                  refine ⟨11643784083930323694914129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7762522722620215796609419 11643784083930323694914129)
                  ·
                    refine ⟨8732838062947742771185597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11643784083930323694914129 8732838062947742771185597)
                    ·
                      refine ⟨3274814273605403539194599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8732838062947742771185597 3274814273605403539194599)
                      ·
                        rfl

theorem cell23_6377678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_6377678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377678 prefixEnd_6377678 := by exact prefixLift 6377678
  have htrace : WordTrace (prefixWord ++ tailWord_6377678) baseStart_6377678 baseEnd_6377678 := by
    simpa [prefixWord, tailWord_6377678, baseEnd_6377678] using wordTrace_append hprefix tailTrace_6377678
  have hstable : (prefixWord ++ tailWord_6377678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377678).length < 2 ^ (prefixWord ++ tailWord_6377678).sum := by decide
  have hdescent : baseEnd_6377678 < baseStart_6377678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377709 : List Nat := [1, 5, 1, 2, 3, 1, 3, 2, 1, 2, 2]
def baseStart_6377709 : Nat := 118140960795 + 6377709 * 2 ^ 59
def prefixEnd_6377709 : Nat := 4983230072969 + 3 ^ 40 * 6377709 * 2
def baseEnd_6377709 : Nat := 3274830191505692917906957

theorem tailTrace_6377709 : CollatzResearch.WordTrace tailWord_6377709 prefixEnd_6377709 3274830191505692917906957 := by
  unfold tailWord_6377709
  simp only [CollatzResearch.WordTrace]
  refine ⟨232614157251656993824600181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155076104834437995883066787 232614157251656993824600181)
  ·
    refine ⟨21807577242342843171056267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232614157251656993824600181 21807577242342843171056267)
    ·
      refine ⟨32711365863514264756584401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21807577242342843171056267 32711365863514264756584401)
      ·
        refine ⟨24533524397635698567438301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32711365863514264756584401 24533524397635698567438301)
        ·
          refine ⟨9200071649113386962789363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24533524397635698567438301 9200071649113386962789363)
          ·
            refine ⟨13800107473670080444184045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9200071649113386962789363 13800107473670080444184045)
            ·
              refine ⟨5175040302626280166569017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13800107473670080444184045 5175040302626280166569017)
              ·
                refine ⟨3881280226969710124926763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5175040302626280166569017 3881280226969710124926763)
                ·
                  refine ⟨5821920340454565187390145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3881280226969710124926763 5821920340454565187390145)
                  ·
                    refine ⟨4366440255340923890542609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5821920340454565187390145 4366440255340923890542609)
                    ·
                      refine ⟨3274830191505692917906957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4366440255340923890542609 3274830191505692917906957)
                      ·
                        rfl

theorem cell23_6377709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_6377709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377709 prefixEnd_6377709 := by exact prefixLift 6377709
  have htrace : WordTrace (prefixWord ++ tailWord_6377709) baseStart_6377709 baseEnd_6377709 := by
    simpa [prefixWord, tailWord_6377709, baseEnd_6377709] using wordTrace_append hprefix tailTrace_6377709
  have hstable : (prefixWord ++ tailWord_6377709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377709).length < 2 ^ (prefixWord ++ tailWord_6377709).sum := by decide
  have hdescent : baseEnd_6377709 < baseStart_6377709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377731 : List Nat := [1, 1, 1, 3, 2, 3, 2, 3, 1, 4, 2]
def baseStart_6377731 : Nat := 118140960795 + 6377731 * 2 ^ 59
def prefixEnd_6377731 : Nat := 4983230072969 + 3 ^ 40 * 6377731 * 2
def baseEnd_6377731 : Nat := 3274841488080091831831855

theorem tailTrace_6377731 : CollatzResearch.WordTrace tailWord_6377731 prefixEnd_6377731 3274841488080091831831855 := by
  unfold tailWord_6377731
  simp only [CollatzResearch.WordTrace]
  refine ⟨232614959657577291581901047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155076639771718194387934031 232614959657577291581901047)
  ·
    refine ⟨348922439486365937372851571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232614959657577291581901047 348922439486365937372851571)
    ·
      refine ⟨523383659229548906059277357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348922439486365937372851571 523383659229548906059277357)
      ·
        refine ⟨196268872211080839772229009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 523383659229548906059277357 196268872211080839772229009)
        ·
          refine ⟨147201654158310629829171757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196268872211080839772229009 147201654158310629829171757)
          ·
            refine ⟨55200620309366486185939409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147201654158310629829171757 55200620309366486185939409)
            ·
              refine ⟨41400465232024864639454557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55200620309366486185939409 41400465232024864639454557)
              ·
                refine ⟨15525174462009324239795459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41400465232024864639454557 15525174462009324239795459)
                ·
                  refine ⟨23287761693013986359693189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15525174462009324239795459 23287761693013986359693189)
                  ·
                    refine ⟨4366455317440122442442473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23287761693013986359693189 4366455317440122442442473)
                    ·
                      refine ⟨3274841488080091831831855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4366455317440122442442473 3274841488080091831831855)
                      ·
                        rfl

theorem cell23_6377731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 4, 2].length) (baseStart_6377731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377731 prefixEnd_6377731 := by exact prefixLift 6377731
  have htrace : WordTrace (prefixWord ++ tailWord_6377731) baseStart_6377731 baseEnd_6377731 := by
    simpa [prefixWord, tailWord_6377731, baseEnd_6377731] using wordTrace_append hprefix tailTrace_6377731
  have hstable : (prefixWord ++ tailWord_6377731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377731).length < 2 ^ (prefixWord ++ tailWord_6377731).sum := by decide
  have hdescent : baseEnd_6377731 < baseStart_6377731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377735 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 3, 3, 2]
def baseStart_6377735 : Nat := 118140960795 + 6377735 * 2 ^ 59
def prefixEnd_6377735 : Nat := 4983230072969 + 3 ^ 40 * 6377735 * 2
def baseEnd_6377735 : Nat := 3274843542002709816181837

theorem tailTrace_6377735 : CollatzResearch.WordTrace tailWord_6377735 prefixEnd_6377735 3274843542002709816181837 := by
  unfold tailWord_6377735
  simp only [CollatzResearch.WordTrace]
  refine ⟨232615105549562800265046659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155076737033041866843364439 232615105549562800265046659)
  ·
    refine ⟨348922658324344200397569989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232615105549562800265046659 348922658324344200397569989)
    ·
      refine ⟨65422998435814537574544373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 348922658324344200397569989 65422998435814537574544373)
      ·
        refine ⟨6133406103357612897613535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65422998435814537574544373 6133406103357612897613535)
        ·
          refine ⟨9200109155036419346420303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6133406103357612897613535 9200109155036419346420303)
          ·
            refine ⟨13800163732554629019630455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9200109155036419346420303 13800163732554629019630455)
            ·
              refine ⟨20700245598831943529445683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13800163732554629019630455 20700245598831943529445683)
              ·
                refine ⟨31050368398247915294168525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20700245598831943529445683 31050368398247915294168525)
                ·
                  refine ⟨11643888149342968235313197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31050368398247915294168525 11643888149342968235313197)
                  ·
                    refine ⟨4366458056003613088242449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11643888149342968235313197 4366458056003613088242449)
                    ·
                      refine ⟨3274843542002709816181837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4366458056003613088242449 3274843542002709816181837)
                      ·
                        rfl

theorem cell23_6377735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_6377735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377735 prefixEnd_6377735 := by exact prefixLift 6377735
  have htrace : WordTrace (prefixWord ++ tailWord_6377735) baseStart_6377735 baseEnd_6377735 := by
    simpa [prefixWord, tailWord_6377735, baseEnd_6377735] using wordTrace_append hprefix tailTrace_6377735
  have hstable : (prefixWord ++ tailWord_6377735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377735).length < 2 ^ (prefixWord ++ tailWord_6377735).sum := by decide
  have hdescent : baseEnd_6377735 < baseStart_6377735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377781 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_6377781 : Nat := 118140960795 + 6377781 * 2 ^ 59
def prefixEnd_6377781 : Nat := 4983230072969 + 3 ^ 40 * 6377781 * 2
def baseEnd_6377781 : Nat := 3274867162112816636206625

theorem tailTrace_6377781 : CollatzResearch.WordTrace tailWord_6377781 prefixEnd_6377781 3274867162112816636206625 := by
  unfold tailWord_6377781
  simp only [CollatzResearch.WordTrace]
  refine ⟨232616783307396150121221197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155077855538264100080814131 232616783307396150121221197)
  ·
    refine ⟨87231293740273556295457949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232616783307396150121221197 87231293740273556295457949)
    ·
      refine ⟨32711735152602583610796731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87231293740273556295457949 32711735152602583610796731)
      ·
        refine ⟨49067602728903875416195097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32711735152602583610796731 49067602728903875416195097)
        ·
          refine ⟨36800702046677906562146323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49067602728903875416195097 36800702046677906562146323)
          ·
            refine ⟨55201053070016859843219485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36800702046677906562146323 55201053070016859843219485)
            ·
              refine ⟨20700394901256322441207307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55201053070016859843219485 20700394901256322441207307)
              ·
                refine ⟨31050592351884483661810961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20700394901256322441207307 31050592351884483661810961)
                ·
                  refine ⟨23287944263913362746358221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31050592351884483661810961 23287944263913362746358221)
                  ·
                    refine ⟨8732979098967511029884333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23287944263913362746358221 8732979098967511029884333)
                    ·
                      refine ⟨3274867162112816636206625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8732979098967511029884333 3274867162112816636206625)
                      ·
                        rfl

theorem cell23_6377781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_6377781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377781 prefixEnd_6377781 := by exact prefixLift 6377781
  have htrace : WordTrace (prefixWord ++ tailWord_6377781) baseStart_6377781 baseEnd_6377781 := by
    simpa [prefixWord, tailWord_6377781, baseEnd_6377781] using wordTrace_append hprefix tailTrace_6377781
  have hstable : (prefixWord ++ tailWord_6377781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377781).length < 2 ^ (prefixWord ++ tailWord_6377781).sum := by decide
  have hdescent : baseEnd_6377781 < baseStart_6377781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377784 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 4, 5]
def baseStart_6377784 : Nat := 118140960795 + 6377784 * 2 ^ 59
def prefixEnd_6377784 : Nat := 4983230072969 + 3 ^ 40 * 6377784 * 2
def baseEnd_6377784 : Nat := 1091622900851593374823037

theorem tailTrace_6377784 : CollatzResearch.WordTrace tailWord_6377784 prefixEnd_6377784 1091622900851593374823037 := by
  unfold tailWord_6377784
  simp only [CollatzResearch.WordTrace]
  refine ⟨116308446363192640816790203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155077928484256854422386937 116308446363192640816790203)
  ·
    refine ⟨174462669544788961225185305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116308446363192640816790203 174462669544788961225185305)
    ·
      refine ⟨130847002158591720918888979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174462669544788961225185305 130847002158591720918888979)
      ·
        refine ⟨196270503237887581378333469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130847002158591720918888979 196270503237887581378333469)
        ·
          refine ⟨73601438714207843016875051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196270503237887581378333469 73601438714207843016875051)
          ·
            refine ⟨110402158071311764525312577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73601438714207843016875051 110402158071311764525312577)
            ·
              refine ⟨82801618553483823393984433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110402158071311764525312577 82801618553483823393984433)
              ·
                refine ⟨62101213915112867545488325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82801618553483823393984433 62101213915112867545488325)
                ·
                  refine ⟨11643977609083662664779061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62101213915112867545488325 11643977609083662664779061)
                  ·
                    refine ⟨1091622900851593374823037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11643977609083662664779061 1091622900851593374823037)
                    ·
                      rfl

theorem cell23_6377784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_6377784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377784 prefixEnd_6377784 := by exact prefixLift 6377784
  have htrace : WordTrace (prefixWord ++ tailWord_6377784) baseStart_6377784 baseEnd_6377784 := by
    simpa [prefixWord, tailWord_6377784, baseEnd_6377784] using wordTrace_append hprefix tailTrace_6377784
  have hstable : (prefixWord ++ tailWord_6377784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377784).length < 2 ^ (prefixWord ++ tailWord_6377784).sum := by decide
  have hdescent : baseEnd_6377784 < baseStart_6377784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377791 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 2, 5, 2]
def baseStart_6377791 : Nat := 118140960795 + 6377791 * 2 ^ 59
def prefixEnd_6377791 : Nat := 4983230072969 + 3 ^ 40 * 6377791 * 2
def baseEnd_6377791 : Nat := 3274872296919361597081579

theorem tailTrace_6377791 : CollatzResearch.WordTrace tailWord_6377791 prefixEnd_6377791 3274872296919361597081579 := by
  unfold tailWord_6377791
  simp only [CollatzResearch.WordTrace]
  refine ⟨232617148037359921829085227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155078098691573281219390151 232617148037359921829085227)
  ·
    refine ⟨348925722056039882743627841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232617148037359921829085227 348925722056039882743627841)
    ·
      refine ⟨261694291542029912057720881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348925722056039882743627841 261694291542029912057720881)
      ·
        refine ⟨196270718656522434043290661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261694291542029912057720881 196270718656522434043290661)
        ·
          refine ⟨36800759748097956383116999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196270718656522434043290661 36800759748097956383116999)
          ·
            refine ⟨55201139622146934574675499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36800759748097956383116999 55201139622146934574675499)
            ·
              refine ⟨82801709433220401862013249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55201139622146934574675499 82801709433220401862013249)
              ·
                refine ⟨62101282074915301396509937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82801709433220401862013249 62101282074915301396509937)
                ·
                  refine ⟨46575961556186476047382453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62101282074915301396509937 46575961556186476047382453)
                  ·
                    refine ⟨4366496395892482129442105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46575961556186476047382453 4366496395892482129442105)
                    ·
                      refine ⟨3274872296919361597081579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4366496395892482129442105 3274872296919361597081579)
                      ·
                        rfl

theorem cell23_6377791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 5, 2].length) (baseStart_6377791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377791 prefixEnd_6377791 := by exact prefixLift 6377791
  have htrace : WordTrace (prefixWord ++ tailWord_6377791) baseStart_6377791 baseEnd_6377791 := by
    simpa [prefixWord, tailWord_6377791, baseEnd_6377791] using wordTrace_append hprefix tailTrace_6377791
  have hstable : (prefixWord ++ tailWord_6377791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377791).length < 2 ^ (prefixWord ++ tailWord_6377791).sum := by decide
  have hdescent : baseEnd_6377791 < baseStart_6377791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377865 : List Nat := [1, 2, 1, 1, 6, 1, 3, 3, 1, 4]
def baseStart_6377865 : Nat := 118140960795 + 6377865 * 2 ^ 59
def prefixEnd_6377865 : Nat := 4983230072969 + 3 ^ 40 * 6377865 * 2
def baseEnd_6377865 : Nat := 1091636764829264769185413

theorem tailTrace_6377865 : CollatzResearch.WordTrace tailWord_6377865 prefixEnd_6377865 1091636764829264769185413 := by
  unfold tailWord_6377865
  simp only [CollatzResearch.WordTrace]
  refine ⟨232619847039091832467279049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155079898026061221644852699 232619847039091832467279049)
  ·
    refine ⟨174464885279318874350459287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232619847039091832467279049 174464885279318874350459287)
    ·
      refine ⟨261697327918978311525688931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174464885279318874350459287 261697327918978311525688931)
      ·
        refine ⟨392545991878467467288533397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261697327918978311525688931 392545991878467467288533397)
        ·
          refine ⟨18400593369303162529150003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 392545991878467467288533397 18400593369303162529150003)
          ·
            refine ⟨27600890053954743793725005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18400593369303162529150003 27600890053954743793725005)
            ·
              refine ⟨10350333770233028922646877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27600890053954743793725005 10350333770233028922646877)
              ·
                refine ⟨3881375163837385845992579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10350333770233028922646877 3881375163837385845992579)
                ·
                  refine ⟨5822062745756078768988869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3881375163837385845992579 5822062745756078768988869)
                  ·
                    refine ⟨1091636764829264769185413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5822062745756078768988869 1091636764829264769185413)
                    ·
                      rfl

theorem cell23_6377865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 1, 4].length) (baseStart_6377865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377865 prefixEnd_6377865 := by exact prefixLift 6377865
  have htrace : WordTrace (prefixWord ++ tailWord_6377865) baseStart_6377865 baseEnd_6377865 := by
    simpa [prefixWord, tailWord_6377865, baseEnd_6377865] using wordTrace_append hprefix tailTrace_6377865
  have hstable : (prefixWord ++ tailWord_6377865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377865).length < 2 ^ (prefixWord ++ tailWord_6377865).sum := by decide
  have hdescent : baseEnd_6377865 < baseStart_6377865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377882 : List Nat := [3, 1, 1, 4, 1, 3, 3, 2, 1, 4]
def baseStart_6377882 : Nat := 118140960795 + 6377882 * 2 ^ 59
def prefixEnd_6377882 : Nat := 4983230072969 + 3 ^ 40 * 6377882 * 2
def baseEnd_6377882 : Nat := 1091639674552973580347887

theorem tailTrace_6377882 : CollatzResearch.WordTrace tailWord_6377882 prefixEnd_6377882 1091639674552973580347887 := by
  unfold tailWord_6377882
  simp only [CollatzResearch.WordTrace]
  refine ⟨58155116770007561092661975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155080311386686829580431933 58155116770007561092661975)
  ·
    refine ⟨87232675155011341638992963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58155116770007561092661975 87232675155011341638992963)
    ·
      refine ⟨130849012732517012458489445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87232675155011341638992963 130849012732517012458489445)
      ·
        refine ⟨24534189887346939835966771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130849012732517012458489445 24534189887346939835966771)
        ·
          refine ⟨36801284831020409753950157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24534189887346939835966771 36801284831020409753950157)
          ·
            refine ⟨13800481811632653657731309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36801284831020409753950157 13800481811632653657731309)
            ·
              refine ⟨5175180679362245121649241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13800481811632653657731309 5175180679362245121649241)
              ·
                refine ⟨3881385509521683841236931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5175180679362245121649241 3881385509521683841236931)
                ·
                  refine ⟨5822078264282525761855397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3881385509521683841236931 5822078264282525761855397)
                  ·
                    refine ⟨1091639674552973580347887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5822078264282525761855397 1091639674552973580347887)
                    ·
                      rfl

theorem cell23_6377882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 1, 4].length) (baseStart_6377882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377882 prefixEnd_6377882 := by exact prefixLift 6377882
  have htrace : WordTrace (prefixWord ++ tailWord_6377882) baseStart_6377882 baseEnd_6377882 := by
    simpa [prefixWord, tailWord_6377882, baseEnd_6377882] using wordTrace_append hprefix tailTrace_6377882
  have hstable : (prefixWord ++ tailWord_6377882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377882).length < 2 ^ (prefixWord ++ tailWord_6377882).sum := by decide
  have hdescent : baseEnd_6377882 < baseStart_6377882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377895 : List Nat := [1, 1, 6, 1, 1, 4, 2, 1, 6]
def baseStart_6377895 : Nat := 118140960795 + 6377895 * 2 ^ 59
def prefixEnd_6377895 : Nat := 4983230072969 + 3 ^ 40 * 6377895 * 2
def baseEnd_6377895 : Nat := 363880633211936576686789

theorem tailTrace_6377895 : CollatzResearch.WordTrace tailWord_6377895 prefixEnd_6377895 363880633211936576686789 := by
  unfold tailWord_6377895
  simp only [CollatzResearch.WordTrace]
  refine ⟨232620941228983147590871139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155080627485988765060580759 232620941228983147590871139)
  ·
    refine ⟨348931411843474721386306709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232620941228983147590871139 348931411843474721386306709)
    ·
      refine ⟨16356159930162877564983127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 348931411843474721386306709 16356159930162877564983127)
      ·
        refine ⟨24534239895244316347474691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16356159930162877564983127 24534239895244316347474691)
        ·
          refine ⟨36801359842866474521212037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24534239895244316347474691 36801359842866474521212037)
          ·
            refine ⟨6900254970537463972727257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36801359842866474521212037 6900254970537463972727257)
            ·
              refine ⟨5175191227903097979545443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6900254970537463972727257 5175191227903097979545443)
              ·
                refine ⟨7762786841854646969318165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5175191227903097979545443 7762786841854646969318165)
                ·
                  refine ⟨363880633211936576686789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7762786841854646969318165 363880633211936576686789)
                  ·
                    rfl

theorem cell23_6377895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 6].length) (baseStart_6377895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377895 prefixEnd_6377895 := by exact prefixLift 6377895
  have htrace : WordTrace (prefixWord ++ tailWord_6377895) baseStart_6377895 baseEnd_6377895 := by
    simpa [prefixWord, tailWord_6377895, baseEnd_6377895] using wordTrace_append hprefix tailTrace_6377895
  have hstable : (prefixWord ++ tailWord_6377895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377895).length < 2 ^ (prefixWord ++ tailWord_6377895).sum := by decide
  have hdescent : baseEnd_6377895 < baseStart_6377895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377945 : List Nat := [1, 2, 1, 2, 4, 1, 2, 3, 3, 2, 2]
def baseStart_6377945 : Nat := 118140960795 + 6377945 * 2 ^ 59
def prefixEnd_6377945 : Nat := 4983230072969 + 3 ^ 40 * 6377945 * 2
def baseEnd_6377945 : Nat := 3274951372940153994555871

theorem tailTrace_6377945 : CollatzResearch.WordTrace tailWord_6377945 prefixEnd_6377945 3274951372940153994555871 := by
  unfold tailWord_6377945
  simp only [CollatzResearch.WordTrace]
  refine ⟨232622764878802006130191289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155081843252534670753460859 232622764878802006130191289)
  ·
    refine ⟨174467073659101504597643467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232622764878802006130191289 174467073659101504597643467)
    ·
      refine ⟨261700610488652256896465201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174467073659101504597643467 261700610488652256896465201)
      ·
        refine ⟨196275457866489192672348901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261700610488652256896465201 196275457866489192672348901)
        ·
          refine ⟨36801648349966723626065419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196275457866489192672348901 36801648349966723626065419)
          ·
            refine ⟨55202472524950085439098129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36801648349966723626065419 55202472524950085439098129)
            ·
              refine ⟨41401854393712564079323597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55202472524950085439098129 41401854393712564079323597)
              ·
                refine ⟨15525695397642211529746349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41401854393712564079323597 15525695397642211529746349)
                ·
                  refine ⟨5822135774115829323654881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15525695397642211529746349 5822135774115829323654881)
                  ·
                    refine ⟨4366601830586871992741161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5822135774115829323654881 4366601830586871992741161)
                    ·
                      refine ⟨3274951372940153994555871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4366601830586871992741161 3274951372940153994555871)
                      ·
                        rfl

theorem cell23_6377945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 2, 2].length) (baseStart_6377945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377945 prefixEnd_6377945 := by exact prefixLift 6377945
  have htrace : WordTrace (prefixWord ++ tailWord_6377945) baseStart_6377945 baseEnd_6377945 := by
    simpa [prefixWord, tailWord_6377945, baseEnd_6377945] using wordTrace_append hprefix tailTrace_6377945
  have hstable : (prefixWord ++ tailWord_6377945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377945).length < 2 ^ (prefixWord ++ tailWord_6377945).sum := by decide
  have hdescent : baseEnd_6377945 < baseStart_6377945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377951 : List Nat := [1, 1, 2, 3, 3, 2, 3, 8]
def baseStart_6377951 : Nat := 118140960795 + 6377951 * 2 ^ 59
def prefixEnd_6377951 : Nat := 4983230072969 + 3 ^ 40 * 6377951 * 2
def baseEnd_6377951 : Nat := 121294609400891887817809

theorem tailTrace_6377951 : CollatzResearch.WordTrace tailWord_6377951 prefixEnd_6377951 121294609400891887817809 := by
  unfold tailWord_6377951
  simp only [CollatzResearch.WordTrace]
  refine ⟨232622983716780269154909707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155081989144520179436606471 232622983716780269154909707)
  ·
    refine ⟨348934475575170403732364561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232622983716780269154909707 348934475575170403732364561)
    ·
      refine ⟨261700856681377802799273421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348934475575170403732364561 261700856681377802799273421)
      ·
        refine ⟨98137821255516676049727533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261700856681377802799273421 98137821255516676049727533)
        ·
          refine ⟨36801682970818753518647825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98137821255516676049727533 36801682970818753518647825)
          ·
            refine ⟨27601262228114065138985869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36801682970818753518647825 27601262228114065138985869)
            ·
              refine ⟨10350473335542774427119701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27601262228114065138985869 10350473335542774427119701)
              ·
                refine ⟨121294609400891887817809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10350473335542774427119701 121294609400891887817809)
                ·
                  rfl

theorem cell23_6377951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 8].length) (baseStart_6377951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377951 prefixEnd_6377951 := by exact prefixLift 6377951
  have htrace : WordTrace (prefixWord ++ tailWord_6377951) baseStart_6377951 baseEnd_6377951 := by
    simpa [prefixWord, tailWord_6377951, baseEnd_6377951] using wordTrace_append hprefix tailTrace_6377951
  have hstable : (prefixWord ++ tailWord_6377951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377951).length < 2 ^ (prefixWord ++ tailWord_6377951).sum := by decide
  have hdescent : baseEnd_6377951 < baseStart_6377951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377962 : List Nat := [3, 1, 3, 1, 3, 2, 1, 2, 3, 2, 2]
def baseStart_6377962 : Nat := 118140960795 + 6377962 * 2 ^ 59
def prefixEnd_6377962 : Nat := 4983230072969 + 3 ^ 40 * 6377962 * 2
def baseEnd_6377962 : Nat := 3274960102111280428043293

theorem tailTrace_6377962 : CollatzResearch.WordTrace tailWord_6377962 prefixEnd_6377962 3274960102111280428043293 := by
  unfold tailWord_6377962
  simp only [CollatzResearch.WordTrace]
  refine ⟨58155846229935104508390035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155082256613160278689040093 58155846229935104508390035)
  ·
    refine ⟨87233769344902656762585053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58155846229935104508390035 87233769344902656762585053)
    ·
      refine ⟨32712663504338496285969395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87233769344902656762585053 32712663504338496285969395)
      ·
        refine ⟨49068995256507744428954093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32712663504338496285969395 49068995256507744428954093)
        ·
          refine ⟨18400873221190404160857785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49068995256507744428954093 18400873221190404160857785)
          ·
            refine ⟨13800654915892803120643339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18400873221190404160857785 13800654915892803120643339)
            ·
              refine ⟨20700982373839204680965009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13800654915892803120643339 20700982373839204680965009)
              ·
                refine ⟨15525736780379403510723757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20700982373839204680965009 15525736780379403510723757)
                ·
                  refine ⟨5822151292642276316521409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15525736780379403510723757 5822151292642276316521409)
                  ·
                    refine ⟨4366613469481707237391057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5822151292642276316521409 4366613469481707237391057)
                    ·
                      refine ⟨3274960102111280428043293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4366613469481707237391057 3274960102111280428043293)
                      ·
                        rfl

theorem cell23_6377962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_6377962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377962 prefixEnd_6377962 := by exact prefixLift 6377962
  have htrace : WordTrace (prefixWord ++ tailWord_6377962) baseStart_6377962 baseEnd_6377962 := by
    simpa [prefixWord, tailWord_6377962, baseEnd_6377962] using wordTrace_append hprefix tailTrace_6377962
  have hstable : (prefixWord ++ tailWord_6377962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377962).length < 2 ^ (prefixWord ++ tailWord_6377962).sum := by decide
  have hdescent : baseEnd_6377962 < baseStart_6377962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377965 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_6377965 : Nat := 118140960795 + 6377965 * 2 ^ 59
def prefixEnd_6377965 : Nat := 4983230072969 + 3 ^ 40 * 6377965 * 2
def baseEnd_6377965 : Nat := 3274961642553243916305779

theorem tailTrace_6377965 : CollatzResearch.WordTrace tailWord_6377965 prefixEnd_6377965 3274961642553243916305779 := by
  unfold tailWord_6377965
  simp only [CollatzResearch.WordTrace]
  refine ⟨232623494338729549545919349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155082329559153033030612899 232623494338729549545919349)
  ·
    refine ⟨21808452594255895269929939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232623494338729549545919349 21808452594255895269929939)
    ·
      refine ⟨32712678891383842904894909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21808452594255895269929939 32712678891383842904894909)
      ·
        refine ⟨12267254584268941089335591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32712678891383842904894909 12267254584268941089335591)
        ·
          refine ⟨18400881876403411634003387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12267254584268941089335591 18400881876403411634003387)
          ·
            refine ⟨27601322814605117451005081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18400881876403411634003387 27601322814605117451005081)
            ·
              refine ⟨20700992110953838088253811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27601322814605117451005081 20700992110953838088253811)
              ·
                refine ⟨31051488166430757132380717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20700992110953838088253811 31051488166430757132380717)
                ·
                  refine ⟨11644308062411533924642769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31051488166430757132380717 11644308062411533924642769)
                  ·
                    refine ⟨8733231046808650443482077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11644308062411533924642769 8733231046808650443482077)
                    ·
                      refine ⟨3274961642553243916305779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8733231046808650443482077 3274961642553243916305779)
                      ·
                        rfl

theorem cell23_6377965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_6377965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377965 prefixEnd_6377965 := by exact prefixLift 6377965
  have htrace : WordTrace (prefixWord ++ tailWord_6377965) baseStart_6377965 baseEnd_6377965 := by
    simpa [prefixWord, tailWord_6377965, baseEnd_6377965] using wordTrace_append hprefix tailTrace_6377965
  have hstable : (prefixWord ++ tailWord_6377965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377965).length < 2 ^ (prefixWord ++ tailWord_6377965).sum := by decide
  have hdescent : baseEnd_6377965 < baseStart_6377965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6377995 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 4, 1, 3]
def baseStart_6377995 : Nat := 118140960795 + 6377995 * 2 ^ 59
def prefixEnd_6377995 : Nat := 4983230072969 + 3 ^ 40 * 6377995 * 2
def baseEnd_6377995 : Nat := 3274977046972878798930641

theorem tailTrace_6377995 : CollatzResearch.WordTrace tailWord_6377995 prefixEnd_6377995 3274977046972878798930641 := by
  unfold tailWord_6377995
  simp only [CollatzResearch.WordTrace]
  refine ⟨232624588528620864669511439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155083059019080576446340959 232624588528620864669511439)
  ·
    refine ⟨348936882792931297004267159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232624588528620864669511439 348936882792931297004267159)
    ·
      refine ⟨523405324189396945506400739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348936882792931297004267159 523405324189396945506400739)
      ·
        refine ⟨785107986284095418259601109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523405324189396945506400739 785107986284095418259601109)
        ·
          refine ⟨18400968428533486365459401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 785107986284095418259601109 18400968428533486365459401)
          ·
            refine ⟨13800726321400114774094551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18400968428533486365459401 13800726321400114774094551)
            ·
              refine ⟨20701089482100172161141827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13800726321400114774094551 20701089482100172161141827)
              ·
                refine ⟨31051634223150258241712741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20701089482100172161141827 31051634223150258241712741)
                ·
                  refine ⟨5822181416840673420321139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31051634223150258241712741 5822181416840673420321139)
                  ·
                    refine ⟨8733272125261010130481709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5822181416840673420321139 8733272125261010130481709)
                    ·
                      refine ⟨3274977046972878798930641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8733272125261010130481709 3274977046972878798930641)
                      ·
                        rfl

theorem cell23_6377995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 1, 3].length) (baseStart_6377995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6377995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6377995 prefixEnd_6377995 := by exact prefixLift 6377995
  have htrace : WordTrace (prefixWord ++ tailWord_6377995) baseStart_6377995 baseEnd_6377995 := by
    simpa [prefixWord, tailWord_6377995, baseEnd_6377995] using wordTrace_append hprefix tailTrace_6377995
  have hstable : (prefixWord ++ tailWord_6377995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6377995).length < 2 ^ (prefixWord ++ tailWord_6377995).sum := by decide
  have hdescent : baseEnd_6377995 < baseStart_6377995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6377995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378001 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 4]
def baseStart_6378001 : Nat := 118140960795 + 6378001 * 2 ^ 59
def prefixEnd_6378001 : Nat := 4983230072969 + 3 ^ 40 * 6378001 * 2
def baseEnd_6378001 : Nat := 3274980127856805775455613

theorem tailTrace_6378001 : CollatzResearch.WordTrace tailWord_6378001 prefixEnd_6378001 3274980127856805775455613 := by
  unfold tailWord_6378001
  simp only [CollatzResearch.WordTrace]
  refine ⟨232624807366599127694229857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155083204911066085129486571 232624807366599127694229857)
  ·
    refine ⟨174468605524949345770672393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232624807366599127694229857 174468605524949345770672393)
    ·
      refine ⟨130851454143712009328004295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174468605524949345770672393 130851454143712009328004295)
      ·
        refine ⟨196277181215568013992006443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130851454143712009328004295 196277181215568013992006443)
        ·
          refine ⟨294415771823352020988009665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196277181215568013992006443 294415771823352020988009665)
          ·
            refine ⟨220811828867514015741007249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294415771823352020988009665 220811828867514015741007249)
            ·
              refine ⟨165608871650635511805755437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220811828867514015741007249 165608871650635511805755437)
              ·
                refine ⟨62103326868988316927158289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165608871650635511805755437 62103326868988316927158289)
                ·
                  refine ⟨46577495151741237695368717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62103326868988316927158289 46577495151741237695368717)
                  ·
                    refine ⟨17466560681902964135763269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46577495151741237695368717 17466560681902964135763269)
                    ·
                      refine ⟨3274980127856805775455613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17466560681902964135763269 3274980127856805775455613)
                      ·
                        rfl

theorem cell23_6378001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_6378001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378001 prefixEnd_6378001 := by exact prefixLift 6378001
  have htrace : WordTrace (prefixWord ++ tailWord_6378001) baseStart_6378001 baseEnd_6378001 := by
    simpa [prefixWord, tailWord_6378001, baseEnd_6378001] using wordTrace_append hprefix tailTrace_6378001
  have hstable : (prefixWord ++ tailWord_6378001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378001).length < 2 ^ (prefixWord ++ tailWord_6378001).sum := by decide
  have hdescent : baseEnd_6378001 < baseStart_6378001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378035 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 6, 2, 2]
def baseStart_6378035 : Nat := 118140960795 + 6378035 * 2 ^ 59
def prefixEnd_6378035 : Nat := 4983230072969 + 3 ^ 40 * 6378035 * 2
def baseEnd_6378035 : Nat := 3274997586199058642430457

theorem tailTrace_6378035 : CollatzResearch.WordTrace tailWord_6378035 prefixEnd_6378035 3274997586199058642430457 := by
  unfold tailWord_6378035
  simp only [CollatzResearch.WordTrace]
  refine ⟨232626047448475951500967559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155084031632317301000645039 232626047448475951500967559)
  ·
    refine ⟨348939071172713927251451339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232626047448475951500967559 348939071172713927251451339)
    ·
      refine ⟨523408606759070890877177009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348939071172713927251451339 523408606759070890877177009)
      ·
        refine ⟨392556455069303168157882757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523408606759070890877177009 392556455069303168157882757)
        ·
          refine ⟨73604335325494344029603017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 392556455069303168157882757 73604335325494344029603017)
          ·
            refine ⟨55203251494120758022202263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73604335325494344029603017 55203251494120758022202263)
            ·
              refine ⟨82804877241181137033303395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55203251494120758022202263 82804877241181137033303395)
              ·
                refine ⟨124207315861771705549955093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82804877241181137033303395 124207315861771705549955093)
                ·
                  refine ⟨5822217931020548697654145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124207315861771705549955093 5822217931020548697654145)
                  ·
                    refine ⟨4366663448265411523240609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5822217931020548697654145 4366663448265411523240609)
                    ·
                      refine ⟨3274997586199058642430457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4366663448265411523240609 3274997586199058642430457)
                      ·
                        rfl

theorem cell23_6378035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 2, 2].length) (baseStart_6378035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378035 prefixEnd_6378035 := by exact prefixLift 6378035
  have htrace : WordTrace (prefixWord ++ tailWord_6378035) baseStart_6378035 baseEnd_6378035 := by
    simpa [prefixWord, tailWord_6378035, baseEnd_6378035] using wordTrace_append hprefix tailTrace_6378035
  have hstable : (prefixWord ++ tailWord_6378035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378035).length < 2 ^ (prefixWord ++ tailWord_6378035).sum := by decide
  have hdescent : baseEnd_6378035 < baseStart_6378035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378058 : List Nat := [3, 1, 2, 1, 1, 4, 3, 1, 7]
def baseStart_6378058 : Nat := 118140960795 + 6378058 * 2 ^ 59
def prefixEnd_6378058 : Nat := 4983230072969 + 3 ^ 40 * 6378058 * 2
def baseEnd_6378058 : Nat := 363889932917123561382539

theorem tailTrace_6378058 : CollatzResearch.WordTrace tailWord_6378058 prefixEnd_6378058 363889932917123561382539 := by
  unfold tailWord_6378058
  simp only [CollatzResearch.WordTrace]
  refine ⟨58156721581848156607263707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155084590884928417619369885 58156721581848156607263707)
  ·
    refine ⟨87235082372772234910895561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58156721581848156607263707 87235082372772234910895561)
    ·
      refine ⟨65426311779579176183171671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87235082372772234910895561 65426311779579176183171671)
      ·
        refine ⟨98139467669368764274757507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65426311779579176183171671 98139467669368764274757507)
        ·
          refine ⟨147209201504053146412136261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98139467669368764274757507 147209201504053146412136261)
          ·
            refine ⟨27601725282009964952275549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147209201504053146412136261 27601725282009964952275549)
            ·
              refine ⟨10350646980753736857103331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27601725282009964952275549 10350646980753736857103331)
              ·
                refine ⟨15525970471130605285654997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10350646980753736857103331 15525970471130605285654997)
                ·
                  refine ⟨363889932917123561382539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15525970471130605285654997 363889932917123561382539)
                  ·
                    rfl

theorem cell23_6378058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 7].length) (baseStart_6378058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378058 prefixEnd_6378058 := by exact prefixLift 6378058
  have htrace : WordTrace (prefixWord ++ tailWord_6378058) baseStart_6378058 baseEnd_6378058 := by
    simpa [prefixWord, tailWord_6378058, baseEnd_6378058] using wordTrace_append hprefix tailTrace_6378058
  have hstable : (prefixWord ++ tailWord_6378058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378058).length < 2 ^ (prefixWord ++ tailWord_6378058).sum := by decide
  have hdescent : baseEnd_6378058 < baseStart_6378058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378069 : List Nat := [1, 3, 2, 2, 1, 1, 6, 1, 2, 2, 2]
def baseStart_6378069 : Nat := 118140960795 + 6378069 * 2 ^ 59
def prefixEnd_6378069 : Nat := 4983230072969 + 3 ^ 40 * 6378069 * 2
def baseEnd_6378069 : Nat := 3275015044541311509405301

theorem tailTrace_6378069 : CollatzResearch.WordTrace tailWord_6378069 prefixEnd_6378069 3275015044541311509405301 := by
  unfold tailWord_6378069
  simp only [CollatzResearch.WordTrace]
  refine ⟨232627287530352775307705261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155084858353568516871803507 232627287530352775307705261)
  ·
    refine ⟨87235232823882290740389473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232627287530352775307705261 87235232823882290740389473)
    ·
      refine ⟨65426424617911718055292105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87235232823882290740389473 65426424617911718055292105)
      ·
        refine ⟨49069818463433788541469079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65426424617911718055292105 49069818463433788541469079)
        ·
          refine ⟨73604727695150682812203619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49069818463433788541469079 73604727695150682812203619)
          ·
            refine ⟨110407091542726024218305429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73604727695150682812203619 110407091542726024218305429)
            ·
              refine ⟨5175332416065282385233067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110407091542726024218305429 5175332416065282385233067)
              ·
                refine ⟨7762998624097923577849601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5175332416065282385233067 7762998624097923577849601)
                ·
                  refine ⟨5822248968073442683387201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7762998624097923577849601 5822248968073442683387201)
                  ·
                    refine ⟨4366686726055082012540401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5822248968073442683387201 4366686726055082012540401)
                    ·
                      refine ⟨3275015044541311509405301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4366686726055082012540401 3275015044541311509405301)
                      ·
                        rfl

theorem cell23_6378069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_6378069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378069 prefixEnd_6378069 := by exact prefixLift 6378069
  have htrace : WordTrace (prefixWord ++ tailWord_6378069) baseStart_6378069 baseEnd_6378069 := by
    simpa [prefixWord, tailWord_6378069, baseEnd_6378069] using wordTrace_append hprefix tailTrace_6378069
  have hstable : (prefixWord ++ tailWord_6378069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378069).length < 2 ^ (prefixWord ++ tailWord_6378069).sum := by decide
  have hdescent : baseEnd_6378069 < baseStart_6378069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378109 : List Nat := [1, 4, 1, 1, 5, 2, 2, 2, 5]
def baseStart_6378109 : Nat := 118140960795 + 6378109 * 2 ^ 59
def prefixEnd_6378109 : Nat := 4983230072969 + 3 ^ 40 * 6378109 * 2
def baseEnd_6378109 : Nat := 363892842640832372545013

theorem tailTrace_6378109 : CollatzResearch.WordTrace tailWord_6378109 prefixEnd_6378109 363892842640832372545013 := by
  unfold tailWord_6378109
  simp only [CollatzResearch.WordTrace]
  refine ⟨232628746450207862139161381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155085830966805241426107587 232628746450207862139161381)
  ·
    refine ⟨43617889959413974151092759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232628746450207862139161381 43617889959413974151092759)
    ·
      refine ⟨65426834939120961226639139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43617889959413974151092759 65426834939120961226639139)
      ·
        refine ⟨98140252408681441839958709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65426834939120961226639139 98140252408681441839958709)
        ·
          refine ⟨9200648663313885172496129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98140252408681441839958709 9200648663313885172496129)
          ·
            refine ⟨6900486497485413879372097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9200648663313885172496129 6900486497485413879372097)
            ·
              refine ⟨5175364873114060409529073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6900486497485413879372097 5175364873114060409529073)
              ·
                refine ⟨3881523654835545307146805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5175364873114060409529073 3881523654835545307146805)
                ·
                  refine ⟨363892842640832372545013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3881523654835545307146805 363892842640832372545013)
                  ·
                    rfl

theorem cell23_6378109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_6378109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378109 prefixEnd_6378109 := by exact prefixLift 6378109
  have htrace : WordTrace (prefixWord ++ tailWord_6378109) baseStart_6378109 baseEnd_6378109 := by
    simpa [prefixWord, tailWord_6378109, baseEnd_6378109] using wordTrace_append hprefix tailTrace_6378109
  have hstable : (prefixWord ++ tailWord_6378109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378109).length < 2 ^ (prefixWord ++ tailWord_6378109).sum := by decide
  have hdescent : baseEnd_6378109 < baseStart_6378109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378135 : List Nat := [1, 1, 3, 3, 2, 1, 3, 2, 3, 4]
def baseStart_6378135 : Nat := 118140960795 + 6378135 * 2 ^ 59
def prefixEnd_6378135 : Nat := 4983230072969 + 3 ^ 40 * 6378135 * 2
def baseEnd_6378135 : Nat := 1091682978088169417059999

theorem tailTrace_6378135 : CollatzResearch.WordTrace tailWord_6378135 prefixEnd_6378135 1091682978088169417059999 := by
  unfold tailWord_6378135
  simp only [CollatzResearch.WordTrace]
  refine ⟨232629694748113668579607859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155086463165409112386405239 232629694748113668579607859)
  ·
    refine ⟨348944542122170502869411789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232629694748113668579607859 348944542122170502869411789)
    ·
      refine ⟨130854203295813938576029421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348944542122170502869411789 130854203295813938576029421)
      ·
        refine ⟨49070326235930226966011033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130854203295813938576029421 49070326235930226966011033)
        ·
          refine ⟨36802744676947670224508275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49070326235930226966011033 36802744676947670224508275)
          ·
            refine ⟨55204117015421505336762413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36802744676947670224508275 55204117015421505336762413)
            ·
              refine ⟨20701543880783064501285905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55204117015421505336762413 20701543880783064501285905)
              ·
                refine ⟨15526157910587298375964429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20701543880783064501285905 15526157910587298375964429)
                ·
                  refine ⟨5822309216470236890986661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15526157910587298375964429 5822309216470236890986661)
                  ·
                    refine ⟨1091682978088169417059999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5822309216470236890986661 1091682978088169417059999)
                    ·
                      rfl

theorem cell23_6378135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 4].length) (baseStart_6378135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378135 prefixEnd_6378135 := by exact prefixLift 6378135
  have htrace : WordTrace (prefixWord ++ tailWord_6378135) baseStart_6378135 baseEnd_6378135 := by
    simpa [prefixWord, tailWord_6378135, baseEnd_6378135] using wordTrace_append hprefix tailTrace_6378135
  have hstable : (prefixWord ++ tailWord_6378135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378135).length < 2 ^ (prefixWord ++ tailWord_6378135).sum := by decide
  have hdescent : baseEnd_6378135 < baseStart_6378135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378142 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_6378142 : Nat := 118140960795 + 6378142 * 2 ^ 59
def prefixEnd_6378142 : Nat := 4983230072969 + 3 ^ 40 * 6378142 * 2
def baseEnd_6378142 : Nat := 3275052528629089723792465

theorem tailTrace_6378142 : CollatzResearch.WordTrace tailWord_6378142 prefixEnd_6378142 3275052528629089723792465 := by
  unfold tailWord_6378142
  simp only [CollatzResearch.WordTrace]
  refine ⟨29078743757386038596889085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155086633372725539183408453 29078743757386038596889085)
  ·
    refine ⟨10904528909019764473833407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29078743757386038596889085 10904528909019764473833407)
    ·
      refine ⟨16356793363529646710750111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10904528909019764473833407 16356793363529646710750111)
      ·
        refine ⟨24535190045294470066125167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16356793363529646710750111 24535190045294470066125167)
        ·
          refine ⟨36802785067941705099187751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24535190045294470066125167 36802785067941705099187751)
          ·
            refine ⟨55204177601912557648781627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36802785067941705099187751 55204177601912557648781627)
            ·
              refine ⟨82806266402868836473172441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55204177601912557648781627 82806266402868836473172441)
              ·
                refine ⟨62104699802151627354879331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82806266402868836473172441 62104699802151627354879331)
                ·
                  refine ⟨93157049703227441032318997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62104699802151627354879331 93157049703227441032318997)
                  ·
                    refine ⟨4366736704838786298389953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93157049703227441032318997 4366736704838786298389953)
                    ·
                      refine ⟨3275052528629089723792465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4366736704838786298389953 3275052528629089723792465)
                      ·
                        rfl

theorem cell23_6378142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_6378142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378142 prefixEnd_6378142 := by exact prefixLift 6378142
  have htrace : WordTrace (prefixWord ++ tailWord_6378142) baseStart_6378142 baseEnd_6378142 := by
    simpa [prefixWord, tailWord_6378142, baseEnd_6378142] using wordTrace_append hprefix tailTrace_6378142
  have hstable : (prefixWord ++ tailWord_6378142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378142).length < 2 ^ (prefixWord ++ tailWord_6378142).sum := by decide
  have hdescent : baseEnd_6378142 < baseStart_6378142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378148 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 8]
def baseStart_6378148 : Nat := 118140960795 + 6378148 * 2 ^ 59
def prefixEnd_6378148 : Nat := 4983230072969 + 3 ^ 40 * 6378148 * 2
def baseEnd_6378148 : Nat := 363895067723668522257493

theorem tailTrace_6378148 : CollatzResearch.WordTrace tailWord_6378148 prefixEnd_6378148 363895067723668522257493 := by
  unfold tailWord_6378148
  simp only [CollatzResearch.WordTrace]
  refine ⟨116315084448533285899915549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155086779264711047866554065 116315084448533285899915549)
  ·
    refine ⟨43618156668199982212468331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116315084448533285899915549 43618156668199982212468331)
    ·
      refine ⟨65427235002299973318702497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43618156668199982212468331 65427235002299973318702497)
      ·
        refine ⟨49070426251724979989026873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65427235002299973318702497 49070426251724979989026873)
        ·
          refine ⟨36802819688793734991770155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49070426251724979989026873 36802819688793734991770155)
          ·
            refine ⟨55204229533190602487655233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36802819688793734991770155 55204229533190602487655233)
            ·
              refine ⟨41403172149892951865741425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55204229533190602487655233 41403172149892951865741425)
              ·
                refine ⟨31052379112419713899306069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41403172149892951865741425 31052379112419713899306069)
                ·
                  refine ⟨363895067723668522257493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31052379112419713899306069 363895067723668522257493)
                  ·
                    rfl

theorem cell23_6378148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_6378148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378148 prefixEnd_6378148 := by exact prefixLift 6378148
  have htrace : WordTrace (prefixWord ++ tailWord_6378148) baseStart_6378148 baseEnd_6378148 := by
    simpa [prefixWord, tailWord_6378148, baseEnd_6378148] using wordTrace_append hprefix tailTrace_6378148
  have hstable : (prefixWord ++ tailWord_6378148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378148).length < 2 ^ (prefixWord ++ tailWord_6378148).sum := by decide
  have hdescent : baseEnd_6378148 < baseStart_6378148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378165 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 8]
def baseStart_6378165 : Nat := 118140960795 + 6378165 * 2 ^ 59
def prefixEnd_6378165 : Nat := 4983230072969 + 3 ^ 40 * 6378165 * 2
def baseEnd_6378165 : Nat := 363896037631571459311651

theorem tailTrace_6378165 : CollatzResearch.WordTrace tailWord_6378165 prefixEnd_6378165 363896037631571459311651 := by
  unfold tailWord_6378165
  simp only [CollatzResearch.WordTrace]
  refine ⟨232630788938004983703199949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155087192625336655802133299 232630788938004983703199949)
  ·
    refine ⟨87236545851751868888699981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232630788938004983703199949 87236545851751868888699981)
    ·
      refine ⟨32713704694406950833262493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87236545851751868888699981 32713704694406950833262493)
      ·
        refine ⟨12267639260402606562473435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32713704694406950833262493 12267639260402606562473435)
        ·
          refine ⟨18401458890603909843710153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12267639260402606562473435 18401458890603909843710153)
          ·
            refine ⟨13801094167952932382782615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18401458890603909843710153 13801094167952932382782615)
            ·
              refine ⟨20701641251929398574173923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13801094167952932382782615 20701641251929398574173923)
              ·
                refine ⟨31052461877894097861260885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20701641251929398574173923 31052461877894097861260885)
                ·
                  refine ⟨363896037631571459311651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31052461877894097861260885 363896037631571459311651)
                  ·
                    rfl

theorem cell23_6378165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 8].length) (baseStart_6378165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378165 prefixEnd_6378165 := by exact prefixLift 6378165
  have htrace : WordTrace (prefixWord ++ tailWord_6378165) baseStart_6378165 baseEnd_6378165 := by
    simpa [prefixWord, tailWord_6378165, baseEnd_6378165] using wordTrace_append hprefix tailTrace_6378165
  have hstable : (prefixWord ++ tailWord_6378165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378165).length < 2 ^ (prefixWord ++ tailWord_6378165).sum := by decide
  have hdescent : baseEnd_6378165 < baseStart_6378165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378202 : List Nat := [3, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2]
def baseStart_6378202 : Nat := 118140960795 + 6378202 * 2 ^ 59
def prefixEnd_6378202 : Nat := 4983230072969 + 3 ^ 40 * 6378202 * 2
def baseEnd_6378202 : Nat := 3275083337468359489042189

theorem tailTrace_6378202 : CollatzResearch.WordTrace tailWord_6378202 prefixEnd_6378202 3275083337468359489042189 := by
  unfold tailWord_6378202
  simp only [CollatzResearch.WordTrace]
  refine ⟨58158034609717734755574215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155088092292580626014864573 58158034609717734755574215)
  ·
    refine ⟨87237051914576602133361323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58158034609717734755574215 87237051914576602133361323)
    ·
      refine ⟨130855577871864903200041985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87237051914576602133361323 130855577871864903200041985)
      ·
        refine ⟨98141683403898677400031489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130855577871864903200041985 98141683403898677400031489)
        ·
          refine ⟨73606262552924008050023617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98141683403898677400031489 73606262552924008050023617)
          ·
            refine ⟨55204696914693006037517713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73606262552924008050023617 55204696914693006037517713)
            ·
              refine ⟨41403522686019754528138285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55204696914693006037517713 41403522686019754528138285)
              ·
                refine ⟨15526321007257407948051857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41403522686019754528138285 15526321007257407948051857)
                ·
                  refine ⟨11644740755443055961038893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15526321007257407948051857 11644740755443055961038893)
                  ·
                    refine ⟨4366777783291145985389585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11644740755443055961038893 4366777783291145985389585)
                    ·
                      refine ⟨3275083337468359489042189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4366777783291145985389585 3275083337468359489042189)
                      ·
                        rfl

theorem cell23_6378202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_6378202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378202 prefixEnd_6378202 := by exact prefixLift 6378202
  have htrace : WordTrace (prefixWord ++ tailWord_6378202) baseStart_6378202 baseEnd_6378202 := by
    simpa [prefixWord, tailWord_6378202, baseEnd_6378202] using wordTrace_append hprefix tailTrace_6378202
  have hstable : (prefixWord ++ tailWord_6378202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378202).length < 2 ^ (prefixWord ++ tailWord_6378202).sum := by decide
  have hdescent : baseEnd_6378202 < baseStart_6378202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378208 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 3, 6]
def baseStart_6378208 : Nat := 118140960795 + 6378208 * 2 ^ 59
def prefixEnd_6378208 : Nat := 4983230072969 + 3 ^ 40 * 6378208 * 2
def baseEnd_6378208 : Nat := 1091695472784095488522387

theorem tailTrace_6378208 : CollatzResearch.WordTrace tailWord_6378208 prefixEnd_6378208 1091695472784095488522387 := by
  unfold tailWord_6378208
  simp only [CollatzResearch.WordTrace]
  refine ⟨116316178638424601023507639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155088238184566134698010185 116316178638424601023507639)
  ·
    refine ⟨174474267957636901535261459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116316178638424601023507639 174474267957636901535261459)
    ·
      refine ⟨261711401936455352302892189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174474267957636901535261459 261711401936455352302892189)
      ·
        refine ⟨98141775726170757113584571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261711401936455352302892189 98141775726170757113584571)
        ·
          refine ⟨147212663589256135670376857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98141775726170757113584571 147212663589256135670376857)
          ·
            refine ⟨110409497691942101752782643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147212663589256135670376857 110409497691942101752782643)
            ·
              refine ⟨165614246537913152629173965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110409497691942101752782643 165614246537913152629173965)
              ·
                refine ⟨62105342451717432235940237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165614246537913152629173965 62105342451717432235940237)
                ·
                  refine ⟨23289503419394037088477589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62105342451717432235940237 23289503419394037088477589)
                  ·
                    refine ⟨1091695472784095488522387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23289503419394037088477589 1091695472784095488522387)
                    ·
                      rfl

theorem cell23_6378208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3, 6].length) (baseStart_6378208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378208 prefixEnd_6378208 := by exact prefixLift 6378208
  have htrace : WordTrace (prefixWord ++ tailWord_6378208) baseStart_6378208 baseEnd_6378208 := by
    simpa [prefixWord, tailWord_6378208, baseEnd_6378208] using wordTrace_append hprefix tailTrace_6378208
  have hstable : (prefixWord ++ tailWord_6378208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378208).length < 2 ^ (prefixWord ++ tailWord_6378208).sum := by decide
  have hdescent : baseEnd_6378208 < baseStart_6378208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378225 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 4, 4]
def baseStart_6378225 : Nat := 118140960795 + 6378225 * 2 ^ 59
def prefixEnd_6378225 : Nat := 4983230072969 + 3 ^ 40 * 6378225 * 2
def baseEnd_6378225 : Nat := 1091698382507804299684861

theorem tailTrace_6378225 : CollatzResearch.WordTrace tailWord_6378225 prefixEnd_6378225 1091698382507804299684861 := by
  unfold tailWord_6378225
  simp only [CollatzResearch.WordTrace]
  refine ⟨232632977317787613950384129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155088651545191742633589419 232632977317787613950384129)
  ·
    refine ⟨174474732988340710462788097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232632977317787613950384129 174474732988340710462788097)
    ·
      refine ⟨130856049741255532847091073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174474732988340710462788097 130856049741255532847091073)
      ·
        refine ⟨98142037305941649635318305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130856049741255532847091073 98142037305941649635318305)
        ·
          refine ⟨73606527979456237226488729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98142037305941649635318305 73606527979456237226488729)
          ·
            refine ⟨55204895984592177919866547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73606527979456237226488729 55204895984592177919866547)
            ·
              refine ⟨82807343976888266879799821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55204895984592177919866547 82807343976888266879799821)
              ·
                refine ⟨31052753991333100079924933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82807343976888266879799821 31052753991333100079924933)
                ·
                  refine ⟨5822391373374956264985925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31052753991333100079924933 5822391373374956264985925)
                  ·
                    refine ⟨1091698382507804299684861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5822391373374956264985925 1091698382507804299684861)
                    ·
                      rfl

theorem cell23_6378225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 4].length) (baseStart_6378225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378225 prefixEnd_6378225 := by exact prefixLift 6378225
  have htrace : WordTrace (prefixWord ++ tailWord_6378225) baseStart_6378225 baseEnd_6378225 := by
    simpa [prefixWord, tailWord_6378225, baseEnd_6378225] using wordTrace_append hprefix tailTrace_6378225
  have hstable : (prefixWord ++ tailWord_6378225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378225).length < 2 ^ (prefixWord ++ tailWord_6378225).sum := by decide
  have hdescent : baseEnd_6378225 < baseStart_6378225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378266 : List Nat := [3, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2]
def baseStart_6378266 : Nat := 118140960795 + 6378266 * 2 ^ 59
def prefixEnd_6378266 : Nat := 4983230072969 + 3 ^ 40 * 6378266 * 2
def baseEnd_6378266 : Nat := 3275116200230247238641895

theorem tailTrace_6378266 : CollatzResearch.WordTrace tailWord_6378266 prefixEnd_6378266 3275116200230247238641895 := by
  unfold tailWord_6378266
  simp only [CollatzResearch.WordTrace]
  refine ⟨58158618177659769488156663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155089648473759385301751101 58158618177659769488156663)
  ·
    refine ⟨87237927266489654232234995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58158618177659769488156663 87237927266489654232234995)
    ·
      refine ⟨130856890899734481348352493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87237927266489654232234995 130856890899734481348352493)
      ·
        refine ⟨49071334087400430505632185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130856890899734481348352493 49071334087400430505632185)
        ·
          refine ⟨36803500565550322879224139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49071334087400430505632185 36803500565550322879224139)
          ·
            refine ⟨55205250848325484318836209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36803500565550322879224139 55205250848325484318836209)
            ·
              refine ⟨41403938136244113239127157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55205250848325484318836209 41403938136244113239127157)
              ·
                refine ⟨3881619200272885616168171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41403938136244113239127157 3881619200272885616168171)
                ·
                  refine ⟨5822428800409328424252257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3881619200272885616168171 5822428800409328424252257)
                  ·
                    refine ⟨4366821600306996318189193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5822428800409328424252257 4366821600306996318189193)
                    ·
                      refine ⟨3275116200230247238641895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4366821600306996318189193 3275116200230247238641895)
                      ·
                        rfl

theorem cell23_6378266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_6378266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378266 prefixEnd_6378266 := by exact prefixLift 6378266
  have htrace : WordTrace (prefixWord ++ tailWord_6378266) baseStart_6378266 baseEnd_6378266 := by
    simpa [prefixWord, tailWord_6378266, baseEnd_6378266] using wordTrace_append hprefix tailTrace_6378266
  have hstable : (prefixWord ++ tailWord_6378266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378266).length < 2 ^ (prefixWord ++ tailWord_6378266).sum := by decide
  have hdescent : baseEnd_6378266 < baseStart_6378266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378325 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_6378325 : Nat := 118140960795 + 6378325 * 2 ^ 59
def prefixEnd_6378325 : Nat := 4983230072969 + 3 ^ 40 * 6378325 * 2
def baseEnd_6378325 : Nat := 3275146495588862507804123

theorem tailTrace_6378325 : CollatzResearch.WordTrace tailWord_6378325 prefixEnd_6378325 3275146495588862507804123 := by
  unfold tailWord_6378325
  simp only [CollatzResearch.WordTrace]
  refine ⟨232636624617425331029024429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155091083078283554019349619 232636624617425331029024429)
  ·
    refine ⟨87238734231534499135884161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232636624617425331029024429 87238734231534499135884161)
    ·
      refine ⟨65429050673650874351913121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87238734231534499135884161 65429050673650874351913121)
      ·
        refine ⟨49071788005238155763934841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65429050673650874351913121 49071788005238155763934841)
        ·
          refine ⟨36803841003928616822951131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49071788005238155763934841 36803841003928616822951131)
          ·
            refine ⟨55205761505892925234426697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36803841003928616822951131 55205761505892925234426697)
            ·
              refine ⟨41404321129419693925820023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55205761505892925234426697 41404321129419693925820023)
              ·
                refine ⟨62106481694129540888730035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41404321129419693925820023 62106481694129540888730035)
                ·
                  refine ⟨93159722541194311333095053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62106481694129540888730035 93159722541194311333095053)
                  ·
                    refine ⟨34934895952947866749910645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93159722541194311333095053 34934895952947866749910645)
                    ·
                      refine ⟨3275146495588862507804123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34934895952947866749910645 3275146495588862507804123)
                      ·
                        rfl

theorem cell23_6378325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_6378325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378325 prefixEnd_6378325 := by exact prefixLift 6378325
  have htrace : WordTrace (prefixWord ++ tailWord_6378325) baseStart_6378325 baseEnd_6378325 := by
    simpa [prefixWord, tailWord_6378325, baseEnd_6378325] using wordTrace_append hprefix tailTrace_6378325
  have hstable : (prefixWord ++ tailWord_6378325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378325).length < 2 ^ (prefixWord ++ tailWord_6378325).sum := by decide
  have hdescent : baseEnd_6378325 < baseStart_6378325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378332 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 2, 6]
def baseStart_6378332 : Nat := 118140960795 + 6378332 * 2 ^ 59
def prefixEnd_6378332 : Nat := 4983230072969 + 3 ^ 40 * 6378332 * 2
def baseEnd_6378332 : Nat := 1091716696651147993472197

theorem tailTrace_6378332 : CollatzResearch.WordTrace tailWord_6378332 prefixEnd_6378332 1091716696651147993472197 := by
  unfold tailWord_6378332
  simp only [CollatzResearch.WordTrace]
  refine ⟨116318439964199985612264625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155091253285599980816352833 116318439964199985612264625)
  ·
    refine ⟨87238829973149989209198469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116318439964199985612264625 87238829973149989209198469)
    ·
      refine ⟨16357280619965622976724713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87238829973149989209198469 16357280619965622976724713)
      ·
        refine ⟨12267960464974217232543535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16357280619965622976724713 12267960464974217232543535)
        ·
          refine ⟨18401940697461325848815303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12267960464974217232543535 18401940697461325848815303)
          ·
            refine ⟨27602911046191988773222955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18401940697461325848815303 27602911046191988773222955)
            ·
              refine ⟨41404366569287983159834433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27602911046191988773222955 41404366569287983159834433)
              ·
                refine ⟨31053274926965987369875825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41404366569287983159834433 31053274926965987369875825)
                ·
                  refine ⟨23289956195224490527406869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31053274926965987369875825 23289956195224490527406869)
                  ·
                    refine ⟨1091716696651147993472197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23289956195224490527406869 1091716696651147993472197)
                    ·
                      rfl

theorem cell23_6378332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_6378332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378332 prefixEnd_6378332 := by exact prefixLift 6378332
  have htrace : WordTrace (prefixWord ++ tailWord_6378332) baseStart_6378332 baseEnd_6378332 := by
    simpa [prefixWord, tailWord_6378332, baseEnd_6378332] using wordTrace_append hprefix tailTrace_6378332
  have hstable : (prefixWord ++ tailWord_6378332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378332).length < 2 ^ (prefixWord ++ tailWord_6378332).sum := by decide
  have hdescent : baseEnd_6378332 < baseStart_6378332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378335 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 4]
def baseStart_6378335 : Nat := 118140960795 + 6378335 * 2 ^ 59
def prefixEnd_6378335 : Nat := 4983230072969 + 3 ^ 40 * 6378335 * 2
def baseEnd_6378335 : Nat := 3275151630395407468679077

theorem tailTrace_6378335 : CollatzResearch.WordTrace tailWord_6378335 prefixEnd_6378335 3275151630395407468679077 := by
  unfold tailWord_6378335
  simp only [CollatzResearch.WordTrace]
  refine ⟨232636989347389102736888459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155091326231592735157925639 232636989347389102736888459)
  ·
    refine ⟨348955484021083654105332689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232636989347389102736888459 348955484021083654105332689)
    ·
      refine ⟨261716613015812740578999517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348955484021083654105332689 261716613015812740578999517)
      ·
        refine ⟨98143729880929777717124819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261716613015812740578999517 98143729880929777717124819)
        ·
          refine ⟨147215594821394666575687229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98143729880929777717124819 147215594821394666575687229)
          ·
            refine ⟨55205848058022999965882711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147215594821394666575687229 55205848058022999965882711)
            ·
              refine ⟨82808772087034499948824067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55205848058022999965882711 82808772087034499948824067)
              ·
                refine ⟨124213158130551749923236101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82808772087034499948824067 124213158130551749923236101)
                ·
                  refine ⟨23289967149478453110606769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124213158130551749923236101 23289967149478453110606769)
                  ·
                    refine ⟨17467475362108839832955077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23289967149478453110606769 17467475362108839832955077)
                    ·
                      refine ⟨3275151630395407468679077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17467475362108839832955077 3275151630395407468679077)
                      ·
                        rfl

theorem cell23_6378335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_6378335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378335 prefixEnd_6378335 := by exact prefixLift 6378335
  have htrace : WordTrace (prefixWord ++ tailWord_6378335) baseStart_6378335 baseEnd_6378335 := by
    simpa [prefixWord, tailWord_6378335, baseEnd_6378335] using wordTrace_append hprefix tailTrace_6378335
  have hstable : (prefixWord ++ tailWord_6378335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378335).length < 2 ^ (prefixWord ++ tailWord_6378335).sum := by decide
  have hdescent : baseEnd_6378335 < baseStart_6378335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378385 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 5]
def baseStart_6378385 : Nat := 118140960795 + 6378385 * 2 ^ 59
def prefixEnd_6378385 : Nat := 4983230072969 + 3 ^ 40 * 6378385 * 2
def baseEnd_6378385 : Nat := 3275177304428132273053847

theorem tailTrace_6378385 : CollatzResearch.WordTrace tailWord_6378385 prefixEnd_6378385 3275177304428132273053847 := by
  unfold tailWord_6378385
  simp only [CollatzResearch.WordTrace]
  refine ⟨232638812997207961276208609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155092541998138640850805739 232638812997207961276208609)
  ·
    refine ⟨174479109747905970957156457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232638812997207961276208609 174479109747905970957156457)
    ·
      refine ⟨130859332310929478217867343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174479109747905970957156457 130859332310929478217867343)
      ·
        refine ⟨196288998466394217326801015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130859332310929478217867343 196288998466394217326801015)
        ·
          refine ⟨294433497699591325990201523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196288998466394217326801015 294433497699591325990201523)
          ·
            refine ⟨441650246549386988985302285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294433497699591325990201523 441650246549386988985302285)
            ·
              refine ⟨165618842456020120869488357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 441650246549386988985302285 165618842456020120869488357)
              ·
                refine ⟨31053532960503772663029067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165618842456020120869488357 31053532960503772663029067)
                ·
                  refine ⟨46580299440755658994543601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31053532960503772663029067 46580299440755658994543601)
                  ·
                    refine ⟨34935224580566744245907701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46580299440755658994543601 34935224580566744245907701)
                    ·
                      refine ⟨3275177304428132273053847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34935224580566744245907701 3275177304428132273053847)
                      ·
                        rfl

theorem cell23_6378385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_6378385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378385 prefixEnd_6378385 := by exact prefixLift 6378385
  have htrace : WordTrace (prefixWord ++ tailWord_6378385) baseStart_6378385 baseEnd_6378385 := by
    simpa [prefixWord, tailWord_6378385, baseEnd_6378385] using wordTrace_append hprefix tailTrace_6378385
  have hstable : (prefixWord ++ tailWord_6378385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378385).length < 2 ^ (prefixWord ++ tailWord_6378385).sum := by decide
  have hdescent : baseEnd_6378385 < baseStart_6378385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378390 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_6378390 : Nat := 118140960795 + 6378390 * 2 ^ 59
def prefixEnd_6378390 : Nat := 4983230072969 + 3 ^ 40 * 6378390 * 2
def baseEnd_6378390 : Nat := 3275179871831404753491325

theorem tailTrace_6378390 : CollatzResearch.WordTrace tailWord_6378390 prefixEnd_6378390 3275179871831404753491325 := by
  unfold tailWord_6378390
  simp only [CollatzResearch.WordTrace]
  refine ⟨14539937210136865445633789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155092663574793231420093749 14539937210136865445633789)
  ·
    refine ⟨5452476453801324542112671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14539937210136865445633789 5452476453801324542112671)
    ·
      refine ⟨8178714680701986813169007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5452476453801324542112671 8178714680701986813169007)
      ·
        refine ⟨12268072021052980219753511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8178714680701986813169007 12268072021052980219753511)
        ·
          refine ⟨18402108031579470329630267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12268072021052980219753511 18402108031579470329630267)
          ·
            refine ⟨27603162047369205494445401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18402108031579470329630267 27603162047369205494445401)
            ·
              refine ⟨20702371535526904120834051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27603162047369205494445401 20702371535526904120834051)
              ·
                refine ⟨31053557303290356181251077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20702371535526904120834051 31053557303290356181251077)
                ·
                  refine ⟨5822541994366941783984577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31053557303290356181251077 5822541994366941783984577)
                  ·
                    refine ⟨4366906495775206337988433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5822541994366941783984577 4366906495775206337988433)
                    ·
                      refine ⟨3275179871831404753491325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4366906495775206337988433 3275179871831404753491325)
                      ·
                        rfl

theorem cell23_6378390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_6378390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378390 prefixEnd_6378390 := by exact prefixLift 6378390
  have htrace : WordTrace (prefixWord ++ tailWord_6378390) baseStart_6378390 baseEnd_6378390 := by
    simpa [prefixWord, tailWord_6378390, baseEnd_6378390] using wordTrace_append hprefix tailTrace_6378390
  have hstable : (prefixWord ++ tailWord_6378390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378390).length < 2 ^ (prefixWord ++ tailWord_6378390).sum := by decide
  have hdescent : baseEnd_6378390 < baseStart_6378390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378396 : List Nat := [2, 2, 3, 3, 3, 1, 1, 1, 7]
def baseStart_6378396 : Nat := 118140960795 + 6378396 * 2 ^ 59
def prefixEnd_6378396 : Nat := 4983230072969 + 3 ^ 40 * 6378396 * 2
def baseEnd_6378396 : Nat := 363909216968370192224033

theorem tailTrace_6378396 : CollatzResearch.WordTrace tailWord_6378396 prefixEnd_6378396 363909216968370192224033 := by
  unfold tailWord_6378396
  simp only [CollatzResearch.WordTrace]
  refine ⟨116319607100084055077429521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155092809466778740103239361 116319607100084055077429521)
  ·
    refine ⟨87239705325063041308072141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116319607100084055077429521 87239705325063041308072141)
    ·
      refine ⟨32714889496898640490527053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87239705325063041308072141 32714889496898640490527053)
      ·
        refine ⟨12268083561336990183947645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32714889496898640490527053 12268083561336990183947645)
        ·
          refine ⟨4600531335501371318980367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12268083561336990183947645 4600531335501371318980367)
          ·
            refine ⟨6900797003252056978470551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4600531335501371318980367 6900797003252056978470551)
            ·
              refine ⟨10351195504878085467705827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6900797003252056978470551 10351195504878085467705827)
              ·
                refine ⟨15526793257317128201558741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10351195504878085467705827 15526793257317128201558741)
                ·
                  refine ⟨363909216968370192224033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15526793257317128201558741 363909216968370192224033)
                  ·
                    rfl

theorem cell23_6378396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 7].length) (baseStart_6378396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378396 prefixEnd_6378396 := by exact prefixLift 6378396
  have htrace : WordTrace (prefixWord ++ tailWord_6378396) baseStart_6378396 baseEnd_6378396 := by
    simpa [prefixWord, tailWord_6378396, baseEnd_6378396] using wordTrace_append hprefix tailTrace_6378396
  have hstable : (prefixWord ++ tailWord_6378396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378396).length < 2 ^ (prefixWord ++ tailWord_6378396).sum := by decide
  have hdescent : baseEnd_6378396 < baseStart_6378396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378402 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_6378402 : Nat := 118140960795 + 6378402 * 2 ^ 59
def prefixEnd_6378402 : Nat := 4983230072969 + 3 ^ 40 * 6378402 * 2
def baseEnd_6378402 : Nat := 3275186033599258706541269

theorem tailTrace_6378402 : CollatzResearch.WordTrace tailWord_6378402 prefixEnd_6378402 3275186033599258706541269 := by
  unfold tailWord_6378402
  simp only [CollatzResearch.WordTrace]
  refine ⟨58159858259536593294894365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155092955358764248786384973 58159858259536593294894365)
  ·
    refine ⟨21809946847326222485585387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58159858259536593294894365 21809946847326222485585387)
    ·
      refine ⟨32714920270989333728378081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21809946847326222485585387 32714920270989333728378081)
      ·
        refine ⟨24536190203242000296283561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32714920270989333728378081 24536190203242000296283561)
        ·
          refine ⟨18402142652431500222212671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24536190203242000296283561 18402142652431500222212671)
          ·
            refine ⟨27603213978647250333319007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18402142652431500222212671 27603213978647250333319007)
            ·
              refine ⟨41404820967970875499978511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27603213978647250333319007 41404820967970875499978511)
              ·
                refine ⟨62107231451956313249967767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41404820967970875499978511 62107231451956313249967767)
                ·
                  refine ⟨93160847177934469874951651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62107231451956313249967767 93160847177934469874951651)
                  ·
                    refine ⟨139741270766901704812427477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93160847177934469874951651 139741270766901704812427477)
                    ·
                      refine ⟨3275186033599258706541269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139741270766901704812427477 3275186033599258706541269)
                      ·
                        rfl

theorem cell23_6378402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_6378402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378402 prefixEnd_6378402 := by exact prefixLift 6378402
  have htrace : WordTrace (prefixWord ++ tailWord_6378402) baseStart_6378402 baseEnd_6378402 := by
    simpa [prefixWord, tailWord_6378402, baseEnd_6378402] using wordTrace_append hprefix tailTrace_6378402
  have hstable : (prefixWord ++ tailWord_6378402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378402).length < 2 ^ (prefixWord ++ tailWord_6378402).sum := by decide
  have hdescent : baseEnd_6378402 < baseStart_6378402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378407 : List Nat := [1, 1, 6, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_6378407 : Nat := 118140960795 + 6378407 * 2 ^ 59
def prefixEnd_6378407 : Nat := 4983230072969 + 3 ^ 40 * 6378407 * 2
def baseEnd_6378407 : Nat := 3275188601002531186978747

theorem tailTrace_6378407 : CollatzResearch.WordTrace tailWord_6378407 prefixEnd_6378407 3275188601002531186978747 := by
  unfold tailWord_6378407
  simp only [CollatzResearch.WordTrace]
  refine ⟨232639615403128259033509475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155093076935418839355672983 232639615403128259033509475)
  ·
    refine ⟨348959423104692388550264213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232639615403128259033509475 348959423104692388550264213)
    ·
      refine ⟨16357472958032455713293635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 348959423104692388550264213 16357472958032455713293635)
      ·
        refine ⟨24536209437048683569940453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16357472958032455713293635 24536209437048683569940453)
        ·
          refine ⟨4600539269446628169363835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24536209437048683569940453 4600539269446628169363835)
          ·
            refine ⟨6900808904169942254045753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4600539269446628169363835 6900808904169942254045753)
            ·
              refine ⟨5175606678127456690534315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6900808904169942254045753 5175606678127456690534315)
              ·
                refine ⟨7763410017191185035801473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5175606678127456690534315 7763410017191185035801473)
                ·
                  refine ⟨5822557512893388776851105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7763410017191185035801473 5822557512893388776851105)
                  ·
                    refine ⟨4366918134670041582638329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5822557512893388776851105 4366918134670041582638329)
                    ·
                      refine ⟨3275188601002531186978747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4366918134670041582638329 3275188601002531186978747)
                      ·
                        rfl

theorem cell23_6378407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_6378407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378407 prefixEnd_6378407 := by exact prefixLift 6378407
  have htrace : WordTrace (prefixWord ++ tailWord_6378407) baseStart_6378407 baseEnd_6378407 := by
    simpa [prefixWord, tailWord_6378407, baseEnd_6378407] using wordTrace_append hprefix tailTrace_6378407
  have hstable : (prefixWord ++ tailWord_6378407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378407).length < 2 ^ (prefixWord ++ tailWord_6378407).sum := by decide
  have hdescent : baseEnd_6378407 < baseStart_6378407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378456 : List Nat := [2, 1, 2, 2, 2, 4, 1, 4, 1, 4]
def baseStart_6378456 : Nat := 118140960795 + 6378456 * 2 ^ 59
def prefixEnd_6378456 : Nat := 4983230072969 + 3 ^ 40 * 6378456 * 2
def baseEnd_6378456 : Nat := 1091737920518200498422007

theorem tailTrace_6378456 : CollatzResearch.WordTrace tailWord_6378456 prefixEnd_6378456 1091737920518200498422007 := by
  unfold tailWord_6378456
  simp only [CollatzResearch.WordTrace]
  refine ⟨116320701289975370201021611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155094268386633826934695481 116320701289975370201021611)
  ·
    refine ⟨174481051934963055301532417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116320701289975370201021611 174481051934963055301532417)
    ·
      refine ⟨130860788951222291476149313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174481051934963055301532417 130860788951222291476149313)
      ·
        refine ⟨98145591713416718607111985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130860788951222291476149313 98145591713416718607111985)
        ·
          refine ⟨73609193785062538955333989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98145591713416718607111985 73609193785062538955333989)
          ·
            refine ⟨13801723834699226054125123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73609193785062538955333989 13801723834699226054125123)
            ·
              refine ⟨20702585752048839081187685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13801723834699226054125123 20702585752048839081187685)
              ·
                refine ⟨3881734828509157327722691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20702585752048839081187685 3881734828509157327722691)
                ·
                  refine ⟨5822602242763735991584037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3881734828509157327722691 5822602242763735991584037)
                  ·
                    refine ⟨1091737920518200498422007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5822602242763735991584037 1091737920518200498422007)
                    ·
                      rfl

theorem cell23_6378456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 1, 4].length) (baseStart_6378456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378456 prefixEnd_6378456 := by exact prefixLift 6378456
  have htrace : WordTrace (prefixWord ++ tailWord_6378456) baseStart_6378456 baseEnd_6378456 := by
    simpa [prefixWord, tailWord_6378456, baseEnd_6378456] using wordTrace_append hprefix tailTrace_6378456
  have hstable : (prefixWord ++ tailWord_6378456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378456).length < 2 ^ (prefixWord ++ tailWord_6378456).sum := by decide
  have hdescent : baseEnd_6378456 < baseStart_6378456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378479 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 5, 1, 3]
def baseStart_6378479 : Nat := 118140960795 + 6378479 * 2 ^ 59
def prefixEnd_6378479 : Nat := 4983230072969 + 3 ^ 40 * 6378479 * 2
def baseEnd_6378479 : Nat := 3275225571609654905278415

theorem tailTrace_6378479 : CollatzResearch.WordTrace tailWord_6378479 prefixEnd_6378479 3275225571609654905278415 := by
  unfold tailWord_6378479
  simp only [CollatzResearch.WordTrace]
  refine ⟨232642241458867415330130491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155094827639244943553420327 232642241458867415330130491)
  ·
    refine ⟨348963362188301122995195737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232642241458867415330130491 348963362188301122995195737)
    ·
      refine ⟨261722521641225842246396803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348963362188301122995195737 261722521641225842246396803)
      ·
        refine ⟨392583782461838763369595205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261722521641225842246396803 392583782461838763369595205)
        ·
          refine ⟨73609459211594768131799101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 392583782461838763369595205 73609459211594768131799101)
          ·
            refine ⟨27603547204348038049424663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73609459211594768131799101 27603547204348038049424663)
            ·
              refine ⟨41405320806522057074136995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27603547204348038049424663 41405320806522057074136995)
              ·
                refine ⟨62107981209783085611205493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41405320806522057074136995 62107981209783085611205493)
                ·
                  refine ⟨5822623238417164276050515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62107981209783085611205493 5822623238417164276050515)
                  ·
                    refine ⟨8733934857625746414075773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5822623238417164276050515 8733934857625746414075773)
                    ·
                      refine ⟨3275225571609654905278415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8733934857625746414075773 3275225571609654905278415)
                      ·
                        rfl

theorem cell23_6378479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 1, 3].length) (baseStart_6378479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378479 prefixEnd_6378479 := by exact prefixLift 6378479
  have htrace : WordTrace (prefixWord ++ tailWord_6378479) baseStart_6378479 baseEnd_6378479 := by
    simpa [prefixWord, tailWord_6378479, baseEnd_6378479] using wordTrace_append hprefix tailTrace_6378479
  have hstable : (prefixWord ++ tailWord_6378479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378479).length < 2 ^ (prefixWord ++ tailWord_6378479).sum := by decide
  have hdescent : baseEnd_6378479 < baseStart_6378479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378489 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 1, 5, 2]
def baseStart_6378489 : Nat := 118140960795 + 6378489 * 2 ^ 59
def prefixEnd_6378489 : Nat := 4983230072969 + 3 ^ 40 * 6378489 * 2
def baseEnd_6378489 : Nat := 3275230706416199866153369

theorem tailTrace_6378489 : CollatzResearch.WordTrace tailWord_6378489 prefixEnd_6378489 3275230706416199866153369 := by
  unfold tailWord_6378489
  simp only [CollatzResearch.WordTrace]
  refine ⟨232642606188831187037994521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155095070792554124691996347 232642606188831187037994521)
  ·
    refine ⟨174481954641623390278495891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232642606188831187037994521 174481954641623390278495891)
    ·
      refine ⟨261722931962435085417743837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174481954641623390278495891 261722931962435085417743837)
      ·
        refine ⟨98146099485913157031653939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261722931962435085417743837 98146099485913157031653939)
        ·
          refine ⟨147219149228869735547480909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98146099485913157031653939 147219149228869735547480909)
          ·
            refine ⟨55207180960826150830305341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147219149228869735547480909 55207180960826150830305341)
            ·
              refine ⟨20702692860309806561364503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55207180960826150830305341 20702692860309806561364503)
              ·
                refine ⟨31054039290464709842046755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20702692860309806561364503 31054039290464709842046755)
                ·
                  refine ⟨46581058935697064763070133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31054039290464709842046755 46581058935697064763070133)
                  ·
                    refine ⟨4366974275221599821537825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46581058935697064763070133 4366974275221599821537825)
                    ·
                      refine ⟨3275230706416199866153369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4366974275221599821537825 3275230706416199866153369)
                      ·
                        rfl

theorem cell23_6378489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_6378489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378489 prefixEnd_6378489 := by exact prefixLift 6378489
  have htrace : WordTrace (prefixWord ++ tailWord_6378489) baseStart_6378489 baseEnd_6378489 := by
    simpa [prefixWord, tailWord_6378489, baseEnd_6378489] using wordTrace_append hprefix tailTrace_6378489
  have hstable : (prefixWord ++ tailWord_6378489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378489).length < 2 ^ (prefixWord ++ tailWord_6378489).sum := by decide
  have hdescent : baseEnd_6378489 < baseStart_6378489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378529 : List Nat := [1, 2, 3, 2, 3, 1, 3, 1, 1, 6]
def baseStart_6378529 : Nat := 118140960795 + 6378529 * 2 ^ 59
def prefixEnd_6378529 : Nat := 4983230072969 + 3 ^ 40 * 6378529 * 2
def baseEnd_6378529 : Nat := 1091750415214126569884395

theorem tailTrace_6378529 : CollatzResearch.WordTrace tailWord_6378529 prefixEnd_6378529 1091750415214126569884395 := by
  unfold tailWord_6378529
  simp only [CollatzResearch.WordTrace]
  refine ⟨232644065108686273869450641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155096043405790849246300427 232644065108686273869450641)
  ·
    refine ⟨174483048831514705402087981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232644065108686273869450641 174483048831514705402087981)
    ·
      refine ⟨65431143311818014525782993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174483048831514705402087981 65431143311818014525782993)
      ·
        refine ⟨49073357483863510894337245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65431143311818014525782993 49073357483863510894337245)
        ·
          refine ⟨18402509056448816585376467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49073357483863510894337245 18402509056448816585376467)
          ·
            refine ⟨27603763584673224878064701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18402509056448816585376467 27603763584673224878064701)
            ·
              refine ⟨10351411344252459329274263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27603763584673224878064701 10351411344252459329274263)
              ·
                refine ⟨15527117016378688993911395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10351411344252459329274263 15527117016378688993911395)
                ·
                  refine ⟨23290675524568033490867093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15527117016378688993911395 23290675524568033490867093)
                  ·
                    refine ⟨1091750415214126569884395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23290675524568033490867093 1091750415214126569884395)
                    ·
                      rfl

theorem cell23_6378529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_6378529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378529 prefixEnd_6378529 := by exact prefixLift 6378529
  have htrace : WordTrace (prefixWord ++ tailWord_6378529) baseStart_6378529 baseEnd_6378529 := by
    simpa [prefixWord, tailWord_6378529, baseEnd_6378529] using wordTrace_append hprefix tailTrace_6378529
  have hstable : (prefixWord ++ tailWord_6378529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378529).length < 2 ^ (prefixWord ++ tailWord_6378529).sum := by decide
  have hdescent : baseEnd_6378529 < baseStart_6378529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378556 : List Nat := [2, 2, 2, 2, 2, 2, 2, 3, 1, 2, 3]
def baseStart_6378556 : Nat := 118140960795 + 6378556 * 2 ^ 59
def prefixEnd_6378556 : Nat := 4983230072969 + 3 ^ 40 * 6378556 * 2
def baseEnd_6378556 : Nat := 3275265109620051104015561

theorem tailTrace_6378556 : CollatzResearch.WordTrace tailWord_6378556 prefixEnd_6378556 3275265109620051104015561 := by
  unfold tailWord_6378556
  simp only [CollatzResearch.WordTrace]
  refine ⟨116322524939794228740341761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155096699919725638320455681 116322524939794228740341761)
  ·
    refine ⟨87241893704845671555256321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116322524939794228740341761 87241893704845671555256321)
    ·
      refine ⟨65431420278634253666442241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87241893704845671555256321 65431420278634253666442241)
      ·
        refine ⟨49073565208975690249831681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65431420278634253666442241 49073565208975690249831681)
        ·
          refine ⟨36805173906731767687373761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49073565208975690249831681 36805173906731767687373761)
          ·
            refine ⟨27603880430048825765530321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36805173906731767687373761 27603880430048825765530321)
            ·
              refine ⟨20702910322536619324147741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27603880430048825765530321 20702910322536619324147741)
              ·
                refine ⟨7763591370951232246555403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20702910322536619324147741 7763591370951232246555403)
                ·
                  refine ⟨11645387056426848369833105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7763591370951232246555403 11645387056426848369833105)
                  ·
                    refine ⟨8734040292320136277374829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11645387056426848369833105 8734040292320136277374829)
                    ·
                      refine ⟨3275265109620051104015561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8734040292320136277374829 3275265109620051104015561)
                      ·
                        rfl

theorem cell23_6378556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_6378556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378556 prefixEnd_6378556 := by exact prefixLift 6378556
  have htrace : WordTrace (prefixWord ++ tailWord_6378556) baseStart_6378556 baseEnd_6378556 := by
    simpa [prefixWord, tailWord_6378556, baseEnd_6378556] using wordTrace_append hprefix tailTrace_6378556
  have hstable : (prefixWord ++ tailWord_6378556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378556).length < 2 ^ (prefixWord ++ tailWord_6378556).sum := by decide
  have hdescent : baseEnd_6378556 < baseStart_6378556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378566 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_6378566 : Nat := 118140960795 + 6378566 * 2 ^ 59
def prefixEnd_6378566 : Nat := 4983230072969 + 3 ^ 40 * 6378566 * 2
def baseEnd_6378566 : Nat := 3275270244426596064890515

theorem tailTrace_6378566 : CollatzResearch.WordTrace tailWord_6378566 prefixEnd_6378566 3275270244426596064890515 := by
  unfold tailWord_6378566
  simp only [CollatzResearch.WordTrace]
  refine ⟨7270169206548507162142111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 155096943073034819459031701 7270169206548507162142111)
  ·
    refine ⟨10905253809822760743213167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7270169206548507162142111 10905253809822760743213167)
    ·
      refine ⟨16357880714734141114819751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10905253809822760743213167 16357880714734141114819751)
      ·
        refine ⟨24536821072101211672229627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16357880714734141114819751 24536821072101211672229627)
        ·
          refine ⟨36805231608151817508344441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24536821072101211672229627 36805231608151817508344441)
          ·
            refine ⟨27603923706113863131258331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36805231608151817508344441 27603923706113863131258331)
            ·
              refine ⟨41405885559170794696887497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27603923706113863131258331 41405885559170794696887497)
              ·
                refine ⟨31054414169378096022665623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41405885559170794696887497 31054414169378096022665623)
                ·
                  refine ⟨46581621254067144033998435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31054414169378096022665623 46581621254067144033998435)
                  ·
                    refine ⟨69872431881100716050997653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46581621254067144033998435 69872431881100716050997653)
                    ·
                      refine ⟨3275270244426596064890515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69872431881100716050997653 3275270244426596064890515)
                      ·
                        rfl

theorem cell23_6378566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_6378566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378566 prefixEnd_6378566 := by exact prefixLift 6378566
  have htrace : WordTrace (prefixWord ++ tailWord_6378566) baseStart_6378566 baseEnd_6378566 := by
    simpa [prefixWord, tailWord_6378566, baseEnd_6378566] using wordTrace_append hprefix tailTrace_6378566
  have hstable : (prefixWord ++ tailWord_6378566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378566).length < 2 ^ (prefixWord ++ tailWord_6378566).sum := by decide
  have hdescent : baseEnd_6378566 < baseStart_6378566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378572 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 2, 7]
def baseStart_6378572 : Nat := 118140960795 + 6378572 * 2 ^ 59
def prefixEnd_6378572 : Nat := 4983230072969 + 3 ^ 40 * 6378572 * 2
def baseEnd_6378572 : Nat := 1091757775103507680471829

theorem tailTrace_6378572 : CollatzResearch.WordTrace tailWord_6378572 prefixEnd_6378572 1091757775103507680471829 := by
  unfold tailWord_6378572
  simp only [CollatzResearch.WordTrace]
  refine ⟨116322816723765246106632985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155097088965020328142177313 116322816723765246106632985)
  ·
    refine ⟨87242112542823934579974739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116322816723765246106632985 87242112542823934579974739)
    ·
      refine ⟨130863168814235901869962109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87242112542823934579974739 130863168814235901869962109)
      ·
        refine ⟨49073688305338463201235791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130863168814235901869962109 49073688305338463201235791)
        ·
          refine ⟨73610532458007694801853687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49073688305338463201235791 73610532458007694801853687)
          ·
            refine ⟨110415798687011542202780531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73610532458007694801853687 110415798687011542202780531)
            ·
              refine ⟨165623698030517313304170797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110415798687011542202780531 165623698030517313304170797)
              ·
                refine ⟨62108886761443992489064049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165623698030517313304170797 62108886761443992489064049)
                ·
                  refine ⟨46581665071082994366798037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62108886761443992489064049 46581665071082994366798037)
                  ·
                    refine ⟨1091757775103507680471829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46581665071082994366798037 1091757775103507680471829)
                    ·
                      rfl

theorem cell23_6378572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_6378572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378572 prefixEnd_6378572 := by exact prefixLift 6378572
  have htrace : WordTrace (prefixWord ++ tailWord_6378572) baseStart_6378572 baseEnd_6378572 := by
    simpa [prefixWord, tailWord_6378572, baseEnd_6378572] using wordTrace_append hprefix tailTrace_6378572
  have hstable : (prefixWord ++ tailWord_6378572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378572).length < 2 ^ (prefixWord ++ tailWord_6378572).sum := by decide
  have hdescent : baseEnd_6378572 < baseStart_6378572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378590 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_6378590 : Nat := 118140960795 + 6378590 * 2 ^ 59
def prefixEnd_6378590 : Nat := 4983230072969 + 3 ^ 40 * 6378590 * 2
def baseEnd_6378590 : Nat := 3275282567962303970990405

theorem tailTrace_6378590 : CollatzResearch.WordTrace tailWord_6378590 prefixEnd_6378590 3275282567962303970990405 := by
  unfold tailWord_6378590
  simp only [CollatzResearch.WordTrace]
  refine ⟨29080786245183160160927653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155097526640976854191614149 29080786245183160160927653)
  ·
    refine ⟨5452647420971842530173935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29080786245183160160927653 5452647420971842530173935)
    ·
      refine ⟨8178971131457763795260903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5452647420971842530173935 8178971131457763795260903)
      ·
        refine ⟨12268456697186645692891355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8178971131457763795260903 12268456697186645692891355)
        ·
          refine ⟨18402685045779968539337033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12268456697186645692891355 18402685045779968539337033)
          ·
            refine ⟨13802013784334976404502775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18402685045779968539337033 13802013784334976404502775)
            ·
              refine ⟨20703020676502464606754163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13802013784334976404502775 20703020676502464606754163)
              ·
                refine ⟨31054531014753696910131245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20703020676502464606754163 31054531014753696910131245)
                ·
                  refine ⟨11645449130532636341299217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31054531014753696910131245 11645449130532636341299217)
                  ·
                    refine ⟨8734086847899477255974413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11645449130532636341299217 8734086847899477255974413)
                    ·
                      refine ⟨3275282567962303970990405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8734086847899477255974413 3275282567962303970990405)
                      ·
                        rfl

theorem cell23_6378590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_6378590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378590 prefixEnd_6378590 := by exact prefixLift 6378590
  have htrace : WordTrace (prefixWord ++ tailWord_6378590) baseStart_6378590 baseEnd_6378590 := by
    simpa [prefixWord, tailWord_6378590, baseEnd_6378590] using wordTrace_append hprefix tailTrace_6378590
  have hstable : (prefixWord ++ tailWord_6378590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378590).length < 2 ^ (prefixWord ++ tailWord_6378590).sum := by decide
  have hdescent : baseEnd_6378590 < baseStart_6378590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378643 : List Nat := [1, 1, 1, 2, 1, 2, 6, 3, 2, 2, 2]
def baseStart_6378643 : Nat := 118140960795 + 6378643 * 2 ^ 59
def prefixEnd_6378643 : Nat := 4983230072969 + 3 ^ 40 * 6378643 * 2
def baseEnd_6378643 : Nat := 3275309782436992263627661

theorem tailTrace_6378643 : CollatzResearch.WordTrace tailWord_6378643 prefixEnd_6378643 3275309782436992263627661 := by
  unfold tailWord_6378643
  simp only [CollatzResearch.WordTrace]
  refine ⟨232648223030273271339100583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155098815353515514226067055 232648223030273271339100583)
  ·
    refine ⟨348972334545409907008650875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232648223030273271339100583 348972334545409907008650875)
    ·
      refine ⟨523458501818114860512976313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348972334545409907008650875 523458501818114860512976313)
      ·
        refine ⟨392593876363586145384732235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523458501818114860512976313 392593876363586145384732235)
        ·
          refine ⟨588890814545379218077098353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392593876363586145384732235 588890814545379218077098353)
          ·
            refine ⟨441668110909034413557823765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588890814545379218077098353 441668110909034413557823765)
            ·
              refine ⟨20703192698860988135522989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 441668110909034413557823765 20703192698860988135522989)
              ·
                refine ⟨7763697262072870550821121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20703192698860988135522989 7763697262072870550821121)
                ·
                  refine ⟨5822772946554652913115841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7763697262072870550821121 5822772946554652913115841)
                  ·
                    refine ⟨4367079709915989684836881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5822772946554652913115841 4367079709915989684836881)
                    ·
                      refine ⟨3275309782436992263627661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4367079709915989684836881 3275309782436992263627661)
                      ·
                        rfl

theorem cell23_6378643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 2, 2].length) (baseStart_6378643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378643 prefixEnd_6378643 := by exact prefixLift 6378643
  have htrace : WordTrace (prefixWord ++ tailWord_6378643) baseStart_6378643 baseEnd_6378643 := by
    simpa [prefixWord, tailWord_6378643, baseEnd_6378643] using wordTrace_append hprefix tailTrace_6378643
  have hstable : (prefixWord ++ tailWord_6378643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378643).length < 2 ^ (prefixWord ++ tailWord_6378643).sum := by decide
  have hdescent : baseEnd_6378643 < baseStart_6378643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378679 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 4, 5]
def baseStart_6378679 : Nat := 118140960795 + 6378679 * 2 ^ 59
def prefixEnd_6378679 : Nat := 4983230072969 + 3 ^ 40 * 6378679 * 2
def baseEnd_6378679 : Nat := 1091776089246851374259165

theorem tailTrace_6378679 : CollatzResearch.WordTrace tailWord_6378679 prefixEnd_6378679 1091776089246851374259165 := by
  unfold tailWord_6378679
  simp only [CollatzResearch.WordTrace]
  refine ⟨232649536058142849487411091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155099690705428566324940727 232649536058142849487411091)
  ·
    refine ⟨348974304087214274231116637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232649536058142849487411091 348974304087214274231116637)
    ·
      refine ⟨130865364032705352836668739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348974304087214274231116637 130865364032705352836668739)
      ·
        refine ⟨196298046049058029255003109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130865364032705352836668739 196298046049058029255003109)
        ·
          refine ⟨36805883634198380485313083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196298046049058029255003109 36805883634198380485313083)
          ·
            refine ⟨55208825451297570727969625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36805883634198380485313083 55208825451297570727969625)
            ·
              refine ⟨41406619088473178045977219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55208825451297570727969625 41406619088473178045977219)
              ·
                refine ⟨62109928632709767068965829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41406619088473178045977219 62109928632709767068965829)
                ·
                  refine ⟨11645611618633081325431093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62109928632709767068965829 11645611618633081325431093)
                  ·
                    refine ⟨1091776089246851374259165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11645611618633081325431093 1091776089246851374259165)
                    ·
                      rfl

theorem cell23_6378679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_6378679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378679 prefixEnd_6378679 := by exact prefixLift 6378679
  have htrace : WordTrace (prefixWord ++ tailWord_6378679) baseStart_6378679 baseEnd_6378679 := by
    simpa [prefixWord, tailWord_6378679, baseEnd_6378679] using wordTrace_append hprefix tailTrace_6378679
  have hstable : (prefixWord ++ tailWord_6378679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378679).length < 2 ^ (prefixWord ++ tailWord_6378679).sum := by decide
  have hdescent : baseEnd_6378679 < baseStart_6378679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378699 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 4]
def baseStart_6378699 : Nat := 118140960795 + 6378699 * 2 ^ 59
def prefixEnd_6378699 : Nat := 4983230072969 + 3 ^ 40 * 6378699 * 2
def baseEnd_6378699 : Nat := 3275338537353644044527403

theorem tailTrace_6378699 : CollatzResearch.WordTrace tailWord_6378699 prefixEnd_6378699 3275338537353644044527403 := by
  unfold tailWord_6378699
  simp only [CollatzResearch.WordTrace]
  refine ⟨232650265518070392903139151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155100177012046928602092767 232650265518070392903139151)
  ·
    refine ⟨348975398277105589354708727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232650265518070392903139151 348975398277105589354708727)
    ·
      refine ⟨523463097415658384032063091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348975398277105589354708727 523463097415658384032063091)
      ·
        refine ⟨785194646123487576048094637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523463097415658384032063091 785194646123487576048094637)
        ·
          refine ⟨294447992296307841018035489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 785194646123487576048094637 294447992296307841018035489)
          ·
            refine ⟨220835994222230880763526617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294447992296307841018035489 220835994222230880763526617)
            ·
              refine ⟨165626995666673160572644963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220835994222230880763526617 165626995666673160572644963)
              ·
                refine ⟨248440493500009740858967445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165626995666673160572644963 248440493500009740858967445)
                ·
                  refine ⟨11645648132812956602764099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 248440493500009740858967445 11645648132812956602764099)
                  ·
                    refine ⟨17468472199219434904146149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11645648132812956602764099 17468472199219434904146149)
                    ·
                      refine ⟨3275338537353644044527403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17468472199219434904146149 3275338537353644044527403)
                      ·
                        rfl

theorem cell23_6378699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 4].length) (baseStart_6378699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378699 prefixEnd_6378699 := by exact prefixLift 6378699
  have htrace : WordTrace (prefixWord ++ tailWord_6378699) baseStart_6378699 baseEnd_6378699 := by
    simpa [prefixWord, tailWord_6378699, baseEnd_6378699] using wordTrace_append hprefix tailTrace_6378699
  have hstable : (prefixWord ++ tailWord_6378699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378699).length < 2 ^ (prefixWord ++ tailWord_6378699).sum := by decide
  have hdescent : baseEnd_6378699 < baseStart_6378699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378717 : List Nat := [1, 4, 3, 2, 3, 1, 1, 3, 5]
def baseStart_6378717 : Nat := 118140960795 + 6378717 * 2 ^ 59
def prefixEnd_6378717 : Nat := 4983230072969 + 3 ^ 40 * 6378717 * 2
def baseEnd_6378717 : Nat := 363927531111713886011369

theorem tailTrace_6378717 : CollatzResearch.WordTrace tailWord_6378717 prefixEnd_6378717 363927531111713886011369 := by
  unfold tailWord_6378717
  simp only [CollatzResearch.WordTrace]
  refine ⟨232650922032005181977294405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155100614688003454651529603 232650922032005181977294405)
  ·
    refine ⟨43622047881000971620742701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232650922032005181977294405 43622047881000971620742701)
    ·
      refine ⟨16358267955375364357778513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43622047881000971620742701 16358267955375364357778513)
      ·
        refine ⟨12268700966531523268333885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16358267955375364357778513 12268700966531523268333885)
        ·
          refine ⟨4600762862449321225625207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12268700966531523268333885 4600762862449321225625207)
          ·
            refine ⟨6901144293673981838437811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4600762862449321225625207 6901144293673981838437811)
            ·
              refine ⟨10351716440510972757656717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6901144293673981838437811 10351716440510972757656717)
              ·
                refine ⟨3881893665191614784121269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10351716440510972757656717 3881893665191614784121269)
                ·
                  refine ⟨363927531111713886011369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3881893665191614784121269 363927531111713886011369)
                  ·
                    rfl

theorem cell23_6378717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_6378717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378717 prefixEnd_6378717 := by exact prefixLift 6378717
  have htrace : WordTrace (prefixWord ++ tailWord_6378717) baseStart_6378717 baseEnd_6378717 := by
    simpa [prefixWord, tailWord_6378717, baseEnd_6378717] using wordTrace_append hprefix tailTrace_6378717
  have hstable : (prefixWord ++ tailWord_6378717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378717).length < 2 ^ (prefixWord ++ tailWord_6378717).sum := by decide
  have hdescent : baseEnd_6378717 < baseStart_6378717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378733 : List Nat := [1, 5, 1, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_6378733 : Nat := 118140960795 + 6378733 * 2 ^ 59
def prefixEnd_6378733 : Nat := 4983230072969 + 3 ^ 40 * 6378733 * 2
def baseEnd_6378733 : Nat := 3275355995695896911502247

theorem tailTrace_6378733 : CollatzResearch.WordTrace tailWord_6378733 prefixEnd_6378733 3275355995695896911502247 := by
  unfold tailWord_6378733
  simp only [CollatzResearch.WordTrace]
  refine ⟨232651505599947216709876853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155101003733298144473251235 232651505599947216709876853)
  ·
    refine ⟨21811078649995051566550955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232651505599947216709876853 21811078649995051566550955)
    ·
      refine ⟨32716617974992577349826433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21811078649995051566550955 32716617974992577349826433)
      ·
        refine ⟨24537463481244433012369825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32716617974992577349826433 24537463481244433012369825)
        ·
          refine ⟨18403097610933324759277369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24537463481244433012369825 18403097610933324759277369)
          ·
            refine ⟨13802323208199993569458027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18403097610933324759277369 13802323208199993569458027)
            ·
              refine ⟨20703484812299990354187041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13802323208199993569458027 20703484812299990354187041)
              ·
                refine ⟨15527613609224992765640281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20703484812299990354187041 15527613609224992765640281)
                ·
                  refine ⟨11645710206918744574230211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15527613609224992765640281 11645710206918744574230211)
                  ·
                    refine ⟨17468565310378116861345317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11645710206918744574230211 17468565310378116861345317)
                    ·
                      refine ⟨3275355995695896911502247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17468565310378116861345317 3275355995695896911502247)
                      ·
                        rfl

theorem cell23_6378733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_6378733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378733 prefixEnd_6378733 := by exact prefixLift 6378733
  have htrace : WordTrace (prefixWord ++ tailWord_6378733) baseStart_6378733 baseEnd_6378733 := by
    simpa [prefixWord, tailWord_6378733, baseEnd_6378733] using wordTrace_append hprefix tailTrace_6378733
  have hstable : (prefixWord ++ tailWord_6378733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378733).length < 2 ^ (prefixWord ++ tailWord_6378733).sum := by decide
  have hdescent : baseEnd_6378733 < baseStart_6378733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378739 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 8]
def baseStart_6378739 : Nat := 118140960795 + 6378739 * 2 ^ 59
def prefixEnd_6378739 : Nat := 4983230072969 + 3 ^ 40 * 6378739 * 2
def baseEnd_6378739 : Nat := 363928786286647098669691

theorem tailTrace_6378739 : CollatzResearch.WordTrace tailWord_6378739 prefixEnd_6378739 363928786286647098669691 := by
  unfold tailWord_6378739
  simp only [CollatzResearch.WordTrace]
  refine ⟨232651724437925479734595271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155101149625283653156396847 232651724437925479734595271)
  ·
    refine ⟨348977586656888219601892907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232651724437925479734595271 348977586656888219601892907)
    ·
      refine ⟨523466379985332329402839361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348977586656888219601892907 523466379985332329402839361)
      ·
        refine ⟨392599784988999247052129521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523466379985332329402839361 392599784988999247052129521)
        ·
          refine ⟨294449838741749435289097141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392599784988999247052129521 294449838741749435289097141)
          ·
            refine ⟨27604672382039009558352857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 294449838741749435289097141 27604672382039009558352857)
            ·
              refine ⟨20703504286529257168764643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27604672382039009558352857 20703504286529257168764643)
              ·
                refine ⟨31055256429793885753146965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20703504286529257168764643 31055256429793885753146965)
                ·
                  refine ⟨363928786286647098669691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31055256429793885753146965 363928786286647098669691)
                  ·
                    rfl

theorem cell23_6378739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 8].length) (baseStart_6378739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378739 prefixEnd_6378739 := by exact prefixLift 6378739
  have htrace : WordTrace (prefixWord ++ tailWord_6378739) baseStart_6378739 baseEnd_6378739 := by
    simpa [prefixWord, tailWord_6378739, baseEnd_6378739] using wordTrace_append hprefix tailTrace_6378739
  have hstable : (prefixWord ++ tailWord_6378739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378739).length < 2 ^ (prefixWord ++ tailWord_6378739).sum := by decide
  have hdescent : baseEnd_6378739 < baseStart_6378739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378794 : List Nat := [3, 1, 4, 2, 1, 3, 2, 2, 1, 4]
def baseStart_6378794 : Nat := 118140960795 + 6378794 * 2 ^ 59
def prefixEnd_6378794 : Nat := 4983230072969 + 3 ^ 40 * 6378794 * 2
def baseEnd_6378794 : Nat := 1091795772671940390946489

theorem tailTrace_6378794 : CollatzResearch.WordTrace tailWord_6378794 prefixEnd_6378794 1091795772671940390946489 := by
  unfold tailWord_6378794
  simp only [CollatzResearch.WordTrace]
  refine ⟨58163432613181556031961859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155102486968484149418564957 58163432613181556031961859)
  ·
    refine ⟨87245148919772334047942789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58163432613181556031961859 87245148919772334047942789)
    ·
      refine ⟨16358465422457312633989273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87245148919772334047942789 16358465422457312633989273)
      ·
        refine ⟨12268849066842984475491955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16358465422457312633989273 12268849066842984475491955)
        ·
          refine ⟨18403273600264476713237933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12268849066842984475491955 18403273600264476713237933)
          ·
            refine ⟨6901227600099178767464225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18403273600264476713237933 6901227600099178767464225)
            ·
              refine ⟨5175920700074384075598169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6901227600099178767464225 5175920700074384075598169)
              ·
                refine ⟨3881940525055788056698627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5175920700074384075598169 3881940525055788056698627)
                ·
                  refine ⟨5822910787583682085047941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3881940525055788056698627 5822910787583682085047941)
                  ·
                    refine ⟨1091795772671940390946489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5822910787583682085047941 1091795772671940390946489)
                    ·
                      rfl

theorem cell23_6378794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_6378794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378794 prefixEnd_6378794 := by exact prefixLift 6378794
  have htrace : WordTrace (prefixWord ++ tailWord_6378794) baseStart_6378794 baseEnd_6378794 := by
    simpa [prefixWord, tailWord_6378794, baseEnd_6378794] using wordTrace_append hprefix tailTrace_6378794
  have hstable : (prefixWord ++ tailWord_6378794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378794).length < 2 ^ (prefixWord ++ tailWord_6378794).sum := by decide
  have hdescent : baseEnd_6378794 < baseStart_6378794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378799 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 5, 6]
def baseStart_6378799 : Nat := 118140960795 + 6378799 * 2 ^ 59
def prefixEnd_6378799 : Nat := 4983230072969 + 3 ^ 40 * 6378799 * 2
def baseEnd_6378799 : Nat := 1091796628473031217758981

theorem tailTrace_6378799 : CollatzResearch.WordTrace tailWord_6378799 prefixEnd_6378799 1091796628473031217758981 := by
  unfold tailWord_6378799
  simp only [CollatzResearch.WordTrace]
  refine ⟨232653912817708109981779451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155102608545138739987852967 232653912817708109981779451)
  ·
    refine ⟨348980869226562164972669177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232653912817708109981779451 348980869226562164972669177)
    ·
      refine ⟨261735651919921623729501883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348980869226562164972669177 261735651919921623729501883)
      ·
        refine ⟨392603477879882435594252825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261735651919921623729501883 392603477879882435594252825)
        ·
          refine ⟨294452608409911826695689619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392603477879882435594252825 294452608409911826695689619)
          ·
            refine ⟨441678912614867740043534429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294452608409911826695689619 441678912614867740043534429)
            ·
              refine ⟨165629592230575402516325411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 441678912614867740043534429 165629592230575402516325411)
              ·
                refine ⟨248444388345863103774488117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165629592230575402516325411 248444388345863103774488117)
                ·
                  refine ⟨23291661407424665978858261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 248444388345863103774488117 23291661407424665978858261)
                  ·
                    refine ⟨1091796628473031217758981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23291661407424665978858261 1091796628473031217758981)
                    ·
                      rfl

theorem cell23_6378799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 6].length) (baseStart_6378799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378799 prefixEnd_6378799 := by exact prefixLift 6378799
  have htrace : WordTrace (prefixWord ++ tailWord_6378799) baseStart_6378799 baseEnd_6378799 := by
    simpa [prefixWord, tailWord_6378799, baseEnd_6378799] using wordTrace_append hprefix tailTrace_6378799
  have hstable : (prefixWord ++ tailWord_6378799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378799).length < 2 ^ (prefixWord ++ tailWord_6378799).sum := by decide
  have hdescent : baseEnd_6378799 < baseStart_6378799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378800 : List Nat := [2, 1, 1, 1, 2, 2, 5, 4, 1, 1, 3]
def baseStart_6378800 : Nat := 118140960795 + 6378800 * 2 ^ 59
def prefixEnd_6378800 : Nat := 4983230072969 + 3 ^ 40 * 6378800 * 2
def baseEnd_6378800 : Nat := 3275390398899748149364439

theorem tailTrace_6378800 : CollatzResearch.WordTrace tailWord_6378800 prefixEnd_6378800 3275390398899748149364439 := by
  unfold tailWord_6378800
  simp only [CollatzResearch.WordTrace]
  refine ⟨116326974645352243576282927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155102632860469658101710569 116326974645352243576282927)
  ·
    refine ⟨174490461968028365364424391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116326974645352243576282927 174490461968028365364424391)
    ·
      refine ⟨261735692952042548046636587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174490461968028365364424391 261735692952042548046636587)
      ·
        refine ⟨392603539428063822069954881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261735692952042548046636587 392603539428063822069954881)
        ·
          refine ⟨294452654571047866552466161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392603539428063822069954881 294452654571047866552466161)
          ·
            refine ⟨220839490928285899914349621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294452654571047866552466161 220839490928285899914349621)
            ·
              refine ⟨20703702274526803116970277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 220839490928285899914349621 20703702274526803116970277)
              ·
                refine ⟨3881944176473775584431927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20703702274526803116970277 3881944176473775584431927)
                ·
                  refine ⟨5822916264710663376647891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3881944176473775584431927 5822916264710663376647891)
                  ·
                    refine ⟨8734374397065995064971837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5822916264710663376647891 8734374397065995064971837)
                    ·
                      refine ⟨3275390398899748149364439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8734374397065995064971837 3275390398899748149364439)
                      ·
                        rfl

theorem cell23_6378800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 1, 1, 3].length) (baseStart_6378800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378800 prefixEnd_6378800 := by exact prefixLift 6378800
  have htrace : WordTrace (prefixWord ++ tailWord_6378800) baseStart_6378800 baseEnd_6378800 := by
    simpa [prefixWord, tailWord_6378800, baseEnd_6378800] using wordTrace_append hprefix tailTrace_6378800
  have hstable : (prefixWord ++ tailWord_6378800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378800).length < 2 ^ (prefixWord ++ tailWord_6378800).sum := by decide
  have hdescent : baseEnd_6378800 < baseStart_6378800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378816 : List Nat := [2, 1, 1, 2, 2, 1, 6, 1, 1, 6]
def baseStart_6378816 : Nat := 118140960795 + 6378816 * 2 ^ 59
def prefixEnd_6378816 : Nat := 4983230072969 + 3 ^ 40 * 6378816 * 2
def baseEnd_6378816 : Nat := 1091799538196740028921455

theorem tailTrace_6378816 : CollatzResearch.WordTrace tailWord_6378816 prefixEnd_6378816 1091799538196740028921455 := by
  unfold tailWord_6378816
  simp only [CollatzResearch.WordTrace]
  refine ⟨116327266429323260942574151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155103021905764347923432201 116327266429323260942574151)
  ·
    refine ⟨174490899643984891413861227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116327266429323260942574151 174490899643984891413861227)
    ·
      refine ⟨261736349465977337120791841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174490899643984891413861227 261736349465977337120791841)
      ·
        refine ⟨196302262099483002840593881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261736349465977337120791841 196302262099483002840593881)
        ·
          refine ⟨147226696574612252130445411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196302262099483002840593881 147226696574612252130445411)
          ·
            refine ⟨220840044861918378195668117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147226696574612252130445411 220840044861918378195668117)
            ·
              refine ⟨10351877102902423977921943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 220840044861918378195668117 10351877102902423977921943)
              ·
                refine ⟨15527815654353635966882915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10351877102902423977921943 15527815654353635966882915)
                ·
                  refine ⟨23291723481530453950324373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15527815654353635966882915 23291723481530453950324373)
                  ·
                    refine ⟨1091799538196740028921455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23291723481530453950324373 1091799538196740028921455)
                    ·
                      rfl

theorem cell23_6378816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 1, 6].length) (baseStart_6378816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378816 prefixEnd_6378816 := by exact prefixLift 6378816
  have htrace : WordTrace (prefixWord ++ tailWord_6378816) baseStart_6378816 baseEnd_6378816 := by
    simpa [prefixWord, tailWord_6378816, baseEnd_6378816] using wordTrace_append hprefix tailTrace_6378816
  have hstable : (prefixWord ++ tailWord_6378816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378816).length < 2 ^ (prefixWord ++ tailWord_6378816).sum := by decide
  have hdescent : baseEnd_6378816 < baseStart_6378816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378873 : List Nat := [1, 2, 1, 3, 2, 1, 5, 1, 1, 3, 3]
def baseStart_6378873 : Nat := 118140960795 + 6378873 * 2 ^ 59
def prefixEnd_6378873 : Nat := 4983230072969 + 3 ^ 40 * 6378873 * 2
def baseEnd_6378873 : Nat := 3275427882987526363751603

theorem tailTrace_6378873 : CollatzResearch.WordTrace tailWord_6378873 prefixEnd_6378873 3275427882987526363751603 := by
  unfold tailWord_6378873
  simp only [CollatzResearch.WordTrace]
  refine ⟨232656611819440020619973273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155104407879626680413315515 232656611819440020619973273)
  ·
    refine ⟨174492458864580015464979955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232656611819440020619973273 174492458864580015464979955)
    ·
      refine ⟨261738688296870023197469933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174492458864580015464979955 261738688296870023197469933)
      ·
        refine ⟨98152008111326258699051225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261738688296870023197469933 98152008111326258699051225)
        ·
          refine ⟨73614006083494694024288419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98152008111326258699051225 73614006083494694024288419)
          ·
            refine ⟨110421009125242041036432629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73614006083494694024288419 110421009125242041036432629)
            ·
              refine ⟨10351969605491441347165559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110421009125242041036432629 10351969605491441347165559)
              ·
                refine ⟨15527954408237162020748339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10351969605491441347165559 15527954408237162020748339)
                ·
                  refine ⟨23291931612355743031122509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15527954408237162020748339 23291931612355743031122509)
                  ·
                    refine ⟨8734474354633403636670941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23291931612355743031122509 8734474354633403636670941)
                    ·
                      refine ⟨3275427882987526363751603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8734474354633403636670941 3275427882987526363751603)
                      ·
                        rfl

theorem cell23_6378873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_6378873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378873 prefixEnd_6378873 := by exact prefixLift 6378873
  have htrace : WordTrace (prefixWord ++ tailWord_6378873) baseStart_6378873 baseEnd_6378873 := by
    simpa [prefixWord, tailWord_6378873, baseEnd_6378873] using wordTrace_append hprefix tailTrace_6378873
  have hstable : (prefixWord ++ tailWord_6378873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378873).length < 2 ^ (prefixWord ++ tailWord_6378873).sum := by decide
  have hdescent : baseEnd_6378873 < baseStart_6378873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378908 : List Nat := [2, 2, 3, 4, 1, 1, 3, 2, 1, 2, 2]
def baseStart_6378908 : Nat := 118140960795 + 6378908 * 2 ^ 59
def prefixEnd_6378908 : Nat := 4983230072969 + 3 ^ 40 * 6378908 * 2
def baseEnd_6378908 : Nat := 3275445854810433726813943

theorem tailTrace_6378908 : CollatzResearch.WordTrace tailWord_6378908 prefixEnd_6378908 3275445854810433726813943 := by
  unfold tailWord_6378908
  simp only [CollatzResearch.WordTrace]
  refine ⟨116328944187156610798748689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155105258916208814398331585 116328944187156610798748689)
  ·
    refine ⟨87246708140367458099061517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116328944187156610798748689 87246708140367458099061517)
    ·
      refine ⟨32717515552637796787148069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87246708140367458099061517 32717515552637796787148069)
      ·
        refine ⟨6134534166119586897590263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32717515552637796787148069 6134534166119586897590263)
        ·
          refine ⟨9201801249179380346385395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6134534166119586897590263 9201801249179380346385395)
          ·
            refine ⟨13802701873769070519578093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9201801249179380346385395 13802701873769070519578093)
            ·
              refine ⟨5176013202663401444841785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13802701873769070519578093 5176013202663401444841785)
              ·
                refine ⟨3882009901997551083631339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5176013202663401444841785 3882009901997551083631339)
                ·
                  refine ⟨5823014852996326625447009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3882009901997551083631339 5823014852996326625447009)
                  ·
                    refine ⟨4367261139747244969085257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5823014852996326625447009 4367261139747244969085257)
                    ·
                      refine ⟨3275445854810433726813943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4367261139747244969085257 3275445854810433726813943)
                      ·
                        rfl

theorem cell23_6378908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_6378908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378908 prefixEnd_6378908 := by exact prefixLift 6378908
  have htrace : WordTrace (prefixWord ++ tailWord_6378908) baseStart_6378908 baseEnd_6378908 := by
    simpa [prefixWord, tailWord_6378908, baseEnd_6378908] using wordTrace_append hprefix tailTrace_6378908
  have hstable : (prefixWord ++ tailWord_6378908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378908).length < 2 ^ (prefixWord ++ tailWord_6378908).sum := by decide
  have hdescent : baseEnd_6378908 < baseStart_6378908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378916 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_6378916 : Nat := 118140960795 + 6378916 * 2 ^ 59
def prefixEnd_6378916 : Nat := 4983230072969 + 3 ^ 40 * 6378916 * 2
def baseEnd_6378916 : Nat := 3275449962655669695513905

theorem tailTrace_6378916 : CollatzResearch.WordTrace tailWord_6378916 prefixEnd_6378916 3275449962655669695513905 := by
  unfold tailWord_6378916
  simp only [CollatzResearch.WordTrace]
  refine ⟨116329090079142119481894301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155105453438856159309192401 116329090079142119481894301)
  ·
    refine ⟨43623408779678294805710363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116329090079142119481894301 43623408779678294805710363)
    ·
      refine ⟨65435113169517442208565545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43623408779678294805710363 65435113169517442208565545)
      ·
        refine ⟨49076334877138081656424159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65435113169517442208565545 49076334877138081656424159)
        ·
          refine ⟨73614502315707122484636239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49076334877138081656424159 73614502315707122484636239)
          ·
            refine ⟨110421753473560683726954359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73614502315707122484636239 110421753473560683726954359)
            ·
              refine ⟨165632630210341025590431539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110421753473560683726954359 165632630210341025590431539)
              ·
                refine ⟨248448945315511538385647309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165632630210341025590431539 248448945315511538385647309)
                ·
                  refine ⟨93168354493316826894617741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 248448945315511538385647309 93168354493316826894617741)
                  ·
                    refine ⟨34938132934993810085481653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93168354493316826894617741 34938132934993810085481653)
                    ·
                      refine ⟨3275449962655669695513905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34938132934993810085481653 3275449962655669695513905)
                      ·
                        rfl

theorem cell23_6378916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_6378916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378916 prefixEnd_6378916 := by exact prefixLift 6378916
  have htrace : WordTrace (prefixWord ++ tailWord_6378916) baseStart_6378916 baseEnd_6378916 := by
    simpa [prefixWord, tailWord_6378916, baseEnd_6378916] using wordTrace_append hprefix tailTrace_6378916
  have hstable : (prefixWord ++ tailWord_6378916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378916).length < 2 ^ (prefixWord ++ tailWord_6378916).sum := by decide
  have hdescent : baseEnd_6378916 < baseStart_6378916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378930 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2]
def baseStart_6378930 : Nat := 118140960795 + 6378930 * 2 ^ 59
def prefixEnd_6378930 : Nat := 4983230072969 + 3 ^ 40 * 6378930 * 2
def baseEnd_6378930 : Nat := 3275457151384832640738841

theorem tailTrace_6378930 : CollatzResearch.WordTrace tailWord_6378930 prefixEnd_6378930 3275457151384832640738841 := by
  unfold tailWord_6378930
  simp only [CollatzResearch.WordTrace]
  refine ⟨58164672695058379838699561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155105793853489012903198829 58164672695058379838699561)
  ·
    refine ⟨43623504521293784879024671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58164672695058379838699561 43623504521293784879024671)
    ·
      refine ⟨65435256781940677318537007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43623504521293784879024671 65435256781940677318537007)
      ·
        refine ⟨98152885172911015977805511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65435256781940677318537007 98152885172911015977805511)
        ·
          refine ⟨147229327759366523966708267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98152885172911015977805511 147229327759366523966708267)
          ·
            refine ⟨220843991639049785950062401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147229327759366523966708267 220843991639049785950062401)
            ·
              refine ⟨165632993729287339462546801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220843991639049785950062401 165632993729287339462546801)
              ·
                refine ⟨124224745296965504596910101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165632993729287339462546801 124224745296965504596910101)
                ·
                  refine ⟨5823034935795258027980161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124224745296965504596910101 5823034935795258027980161)
                  ·
                    refine ⟨4367276201846443520985121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5823034935795258027980161 4367276201846443520985121)
                    ·
                      refine ⟨3275457151384832640738841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4367276201846443520985121 3275457151384832640738841)
                      ·
                        rfl

theorem cell23_6378930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_6378930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378930 prefixEnd_6378930 := by exact prefixLift 6378930
  have htrace : WordTrace (prefixWord ++ tailWord_6378930) baseStart_6378930 baseEnd_6378930 := by
    simpa [prefixWord, tailWord_6378930, baseEnd_6378930] using wordTrace_append hprefix tailTrace_6378930
  have hstable : (prefixWord ++ tailWord_6378930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378930).length < 2 ^ (prefixWord ++ tailWord_6378930).sum := by decide
  have hdescent : baseEnd_6378930 < baseStart_6378930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378933 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_6378933 : Nat := 118140960795 + 6378933 * 2 ^ 59
def prefixEnd_6378933 : Nat := 4983230072969 + 3 ^ 40 * 6378933 * 2
def baseEnd_6378933 : Nat := 3275458691826796129001327

theorem tailTrace_6378933 : CollatzResearch.WordTrace tailWord_6378933 prefixEnd_6378933 3275458691826796129001327 := by
  unfold tailWord_6378933
  simp only [CollatzResearch.WordTrace]
  refine ⟨232658800199222650867157453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155105866799481767244771635 232658800199222650867157453)
  ·
    refine ⟨87247050074708494075184045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232658800199222650867157453 87247050074708494075184045)
    ·
      refine ⟨32717643778015685278194017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87247050074708494075184045 32717643778015685278194017)
      ·
        refine ⟨24538232833511763958645513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32717643778015685278194017 24538232833511763958645513)
        ·
          refine ⟨18403674625133822968984135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24538232833511763958645513 18403674625133822968984135)
          ·
            refine ⟨27605511937700734453476203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18403674625133822968984135 27605511937700734453476203)
            ·
              refine ⟨41408267906551101680214305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27605511937700734453476203 41408267906551101680214305)
              ·
                refine ⟨31056200929913326260160729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41408267906551101680214305 31056200929913326260160729)
                ·
                  refine ⟨23292150697434994695120547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31056200929913326260160729 23292150697434994695120547)
                  ·
                    refine ⟨34938226046152492042680821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23292150697434994695120547 34938226046152492042680821)
                    ·
                      refine ⟨3275458691826796129001327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34938226046152492042680821 3275458691826796129001327)
                      ·
                        rfl

theorem cell23_6378933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_6378933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378933 prefixEnd_6378933 := by exact prefixLift 6378933
  have htrace : WordTrace (prefixWord ++ tailWord_6378933) baseStart_6378933 baseEnd_6378933 := by
    simpa [prefixWord, tailWord_6378933, baseEnd_6378933] using wordTrace_append hprefix tailTrace_6378933
  have hstable : (prefixWord ++ tailWord_6378933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378933).length < 2 ^ (prefixWord ++ tailWord_6378933).sum := by decide
  have hdescent : baseEnd_6378933 < baseStart_6378933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378936 : List Nat := [2, 1, 2, 1, 2, 2, 2, 4, 7]
def baseStart_6378936 : Nat := 118140960795 + 6378936 * 2 ^ 59
def prefixEnd_6378936 : Nat := 4983230072969 + 3 ^ 40 * 6378936 * 2
def baseEnd_6378936 : Nat := 363940025807639957473757

theorem tailTrace_6378936 : CollatzResearch.WordTrace tailWord_6378936 prefixEnd_6378936 363940025807639957473757 := by
  unfold tailWord_6378936
  simp only [CollatzResearch.WordTrace]
  refine ⟨116329454809105891189758331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155105939745474521586344441 116329454809105891189758331)
  ·
    refine ⟨174494182213658836784637497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116329454809105891189758331 174494182213658836784637497)
    ·
      refine ⟨130870636660244127588478123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174494182213658836784637497 130870636660244127588478123)
      ·
        refine ⟨196305954990366191382717185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130870636660244127588478123 196305954990366191382717185)
        ·
          refine ⟨147229466242774643537037889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196305954990366191382717185 147229466242774643537037889)
          ·
            refine ⟨110422099682080982652778417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147229466242774643537037889 110422099682080982652778417)
            ·
              refine ⟨82816574761560736989583813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110422099682080982652778417 82816574761560736989583813)
              ·
                refine ⟨15528107767792638185546965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82816574761560736989583813 15528107767792638185546965)
                ·
                  refine ⟨363940025807639957473757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15528107767792638185546965 363940025807639957473757)
                  ·
                    rfl

theorem cell23_6378936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 7].length) (baseStart_6378936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378936 prefixEnd_6378936 := by exact prefixLift 6378936
  have htrace : WordTrace (prefixWord ++ tailWord_6378936) baseStart_6378936 baseEnd_6378936 := by
    simpa [prefixWord, tailWord_6378936, baseEnd_6378936] using wordTrace_append hprefix tailTrace_6378936
  have hstable : (prefixWord ++ tailWord_6378936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378936).length < 2 ^ (prefixWord ++ tailWord_6378936).sum := by decide
  have hdescent : baseEnd_6378936 < baseStart_6378936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378953 : List Nat := [1, 2, 1, 1, 2, 1, 3, 7, 5]
def baseStart_6378953 : Nat := 118140960795 + 6378953 * 2 ^ 59
def prefixEnd_6378953 : Nat := 4983230072969 + 3 ^ 40 * 6378953 * 2
def baseEnd_6378953 : Nat := 363940995715542894527915

theorem tailTrace_6378953 : CollatzResearch.WordTrace tailWord_6378953 prefixEnd_6378953 363940995715542894527915 := by
  unfold tailWord_6378953
  simp only [CollatzResearch.WordTrace]
  refine ⟨232659529659150194282885513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155106353106100129521923675 232659529659150194282885513)
  ·
    refine ⟨174494647244362645712164135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232659529659150194282885513 174494647244362645712164135)
    ·
      refine ⟨261741970866543968568246203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174494647244362645712164135 261741970866543968568246203)
      ·
        refine ⟨392612956299815952852369305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261741970866543968568246203 392612956299815952852369305)
        ·
          refine ⟨294459717224861964639276979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392612956299815952852369305 294459717224861964639276979)
          ·
            refine ⟨441689575837292946958915469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294459717224861964639276979 441689575837292946958915469)
            ·
              refine ⟨165633590938984855109593301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 441689575837292946958915469 165633590938984855109593301)
              ·
                refine ⟨3882037287632457541631093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 165633590938984855109593301 3882037287632457541631093)
                ·
                  refine ⟨363940995715542894527915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3882037287632457541631093 363940995715542894527915)
                  ·
                    rfl

theorem cell23_6378953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 5].length) (baseStart_6378953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378953 prefixEnd_6378953 := by exact prefixLift 6378953
  have htrace : WordTrace (prefixWord ++ tailWord_6378953) baseStart_6378953 baseEnd_6378953 := by
    simpa [prefixWord, tailWord_6378953, baseEnd_6378953] using wordTrace_append hprefix tailTrace_6378953
  have hstable : (prefixWord ++ tailWord_6378953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378953).length < 2 ^ (prefixWord ++ tailWord_6378953).sum := by decide
  have hdescent : baseEnd_6378953 < baseStart_6378953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378970 : List Nat := [3, 1, 1, 2, 3, 3, 1, 4, 5]
def baseStart_6378970 : Nat := 118140960795 + 6378970 * 2 ^ 59
def prefixEnd_6378970 : Nat := 4983230072969 + 3 ^ 40 * 6378970 * 2
def baseEnd_6378970 : Nat := 363941965623445831582073

theorem tailTrace_6378970 : CollatzResearch.WordTrace tailWord_6378970 prefixEnd_6378970 363941965623445831582073 := by
  unfold tailWord_6378970
  simp only [CollatzResearch.WordTrace]
  refine ⟨58165037425022151546563591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155106766466725737457502909 58165037425022151546563591)
  ·
    refine ⟨87247556137533227319845387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58165037425022151546563591 87247556137533227319845387)
    ·
      refine ⟨130871334206299840979768081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87247556137533227319845387 130871334206299840979768081)
      ·
        refine ⟨98153500654724880734826061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130871334206299840979768081 98153500654724880734826061)
        ·
          refine ⟨36807562745521830275559773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98153500654724880734826061 36807562745521830275559773)
          ·
            refine ⟨13802836029570686353334915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36807562745521830275559773 13802836029570686353334915)
            ·
              refine ⟨20704254044356029530002373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13802836029570686353334915 20704254044356029530002373)
              ·
                refine ⟨3882047633316755536875445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20704254044356029530002373 3882047633316755536875445)
                ·
                  refine ⟨363941965623445831582073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3882047633316755536875445 363941965623445831582073)
                  ·
                    rfl

theorem cell23_6378970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 5].length) (baseStart_6378970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378970 prefixEnd_6378970 := by exact prefixLift 6378970
  have htrace : WordTrace (prefixWord ++ tailWord_6378970) baseStart_6378970 baseEnd_6378970 := by
    simpa [prefixWord, tailWord_6378970, baseEnd_6378970] using wordTrace_append hprefix tailTrace_6378970
  have hstable : (prefixWord ++ tailWord_6378970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378970).length < 2 ^ (prefixWord ++ tailWord_6378970).sum := by decide
  have hdescent : baseEnd_6378970 < baseStart_6378970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378976 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 7]
def baseStart_6378976 : Nat := 118140960795 + 6378976 * 2 ^ 59
def prefixEnd_6378976 : Nat := 4983230072969 + 3 ^ 40 * 6378976 * 2
def baseEnd_6378976 : Nat := 3275480771494939460763629

theorem tailTrace_6378976 : CollatzResearch.WordTrace tailWord_6378976 prefixEnd_6378976 3275480771494939460763629 := by
  unfold tailWord_6378976
  simp only [CollatzResearch.WordTrace]
  refine ⟨116330184269033434605486391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155106912358711246140648521 116330184269033434605486391)
  ·
    refine ⟨174495276403550151908229587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116330184269033434605486391 174495276403550151908229587)
    ·
      refine ⟨261742914605325227862344381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174495276403550151908229587 261742914605325227862344381)
      ·
        refine ⟨98153592976996960448379143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261742914605325227862344381 98153592976996960448379143)
        ·
          refine ⟨147230389465495440672568715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98153592976996960448379143 147230389465495440672568715)
          ·
            refine ⟨220845584198243161008853073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147230389465495440672568715 220845584198243161008853073)
            ·
              refine ⟨165634188148682370756639805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220845584198243161008853073 165634188148682370756639805)
              ·
                refine ⟨62112820555755889033739927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165634188148682370756639805 62112820555755889033739927)
                ·
                  refine ⟨93169230833633833550609891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62112820555755889033739927 93169230833633833550609891)
                  ·
                    refine ⟨139753846250450750325914837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93169230833633833550609891 139753846250450750325914837)
                    ·
                      refine ⟨3275480771494939460763629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139753846250450750325914837 3275480771494939460763629)
                      ·
                        rfl

theorem cell23_6378976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_6378976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378976 prefixEnd_6378976 := by exact prefixLift 6378976
  have htrace : WordTrace (prefixWord ++ tailWord_6378976) baseStart_6378976 baseEnd_6378976 := by
    simpa [prefixWord, tailWord_6378976, baseEnd_6378976] using wordTrace_append hprefix tailTrace_6378976
  have hstable : (prefixWord ++ tailWord_6378976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378976).length < 2 ^ (prefixWord ++ tailWord_6378976).sum := by decide
  have hdescent : baseEnd_6378976 < baseStart_6378976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6378990 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 2, 5, 2]
def baseStart_6378990 : Nat := 118140960795 + 6378990 * 2 ^ 59
def prefixEnd_6378990 : Nat := 4983230072969 + 3 ^ 40 * 6378990 * 2
def baseEnd_6378990 : Nat := 3275487960224102405988565

theorem tailTrace_6378990 : CollatzResearch.WordTrace tailWord_6378990 prefixEnd_6378990 3275487960224102405988565 := by
  unfold tailWord_6378990
  simp only [CollatzResearch.WordTrace]
  refine ⟨29082609895002018700247803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155107252773344099734654949 29082609895002018700247803)
  ·
    refine ⟨43623914842503028050371705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29082609895002018700247803 43623914842503028050371705)
    ·
      refine ⟨32717936131877271037778779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43623914842503028050371705 32717936131877271037778779)
      ·
        refine ⟨49076904197815906556668169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32717936131877271037778779 49076904197815906556668169)
        ·
          refine ⟨36807678148361929917501127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49076904197815906556668169 36807678148361929917501127)
          ·
            refine ⟨55211517222542894876251691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36807678148361929917501127 55211517222542894876251691)
            ·
              refine ⟨82817275833814342314377537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55211517222542894876251691 82817275833814342314377537)
              ·
                refine ⟨62112956875360756735783153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82817275833814342314377537 62112956875360756735783153)
                ·
                  refine ⟨46584717656520567551837365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62112956875360756735783153 46584717656520567551837365)
                  ·
                    refine ⟨4367317280298803207984753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46584717656520567551837365 4367317280298803207984753)
                    ·
                      refine ⟨3275487960224102405988565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4367317280298803207984753 3275487960224102405988565)
                      ·
                        rfl

theorem cell23_6378990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_6378990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6378990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6378990 prefixEnd_6378990 := by exact prefixLift 6378990
  have htrace : WordTrace (prefixWord ++ tailWord_6378990) baseStart_6378990 baseEnd_6378990 := by
    simpa [prefixWord, tailWord_6378990, baseEnd_6378990] using wordTrace_append hprefix tailTrace_6378990
  have hstable : (prefixWord ++ tailWord_6378990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6378990).length < 2 ^ (prefixWord ++ tailWord_6378990).sum := by decide
  have hdescent : baseEnd_6378990 < baseStart_6378990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6378990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379000 : List Nat := [2, 1, 2, 1, 1, 7, 1, 1, 2, 5]
def baseStart_6379000 : Nat := 118140960795 + 6379000 * 2 ^ 59
def prefixEnd_6379000 : Nat := 4983230072969 + 3 ^ 40 * 6379000 * 2
def baseEnd_6379000 : Nat := 1091831031676882455621173

theorem tailTrace_6379000 : CollatzResearch.WordTrace tailWord_6379000 prefixEnd_6379000 1091831031676882455621173 := by
  unfold tailWord_6379000
  simp only [CollatzResearch.WordTrace]
  refine ⟨116330621944989960654923227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155107495926653280873230969 116330621944989960654923227)
  ·
    refine ⟨174495932917484940982384841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116330621944989960654923227 174495932917484940982384841)
    ·
      refine ⟨130871949688113705736788631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174495932917484940982384841 130871949688113705736788631)
      ·
        refine ⟨196307924532170558605182947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130871949688113705736788631 196307924532170558605182947)
        ·
          refine ⟨294461886798255837907774421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196307924532170558605182947 294461886798255837907774421)
          ·
            refine ⟨6901450471834121200963463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 294461886798255837907774421 6901450471834121200963463)
            ·
              refine ⟨10352175707751181801445195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6901450471834121200963463 10352175707751181801445195)
              ·
                refine ⟨15528263561626772702167793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10352175707751181801445195 15528263561626772702167793)
                ·
                  refine ⟨11646197671220079526625845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15528263561626772702167793 11646197671220079526625845)
                  ·
                    refine ⟨1091831031676882455621173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11646197671220079526625845 1091831031676882455621173)
                    ·
                      rfl

theorem cell23_6379000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 2, 5].length) (baseStart_6379000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379000 prefixEnd_6379000 := by exact prefixLift 6379000
  have htrace : WordTrace (prefixWord ++ tailWord_6379000) baseStart_6379000 baseEnd_6379000 := by
    simpa [prefixWord, tailWord_6379000, baseEnd_6379000] using wordTrace_append hprefix tailTrace_6379000
  have hstable : (prefixWord ++ tailWord_6379000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379000).length < 2 ^ (prefixWord ++ tailWord_6379000).sum := by decide
  have hdescent : baseEnd_6379000 < baseStart_6379000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379013 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 7, 4]
def baseStart_6379013 : Nat := 118140960795 + 6379013 * 2 ^ 59
def prefixEnd_6379013 : Nat := 4983230072969 + 3 ^ 40 * 6379013 * 2
def baseEnd_6379013 : Nat := 1091833256759718605333653

theorem tailTrace_6379013 : CollatzResearch.WordTrace tailWord_6379013 prefixEnd_6379013 1091833256759718605333653 := by
  unfold tailWord_6379013
  simp only [CollatzResearch.WordTrace]
  refine ⟨232661718038932824530069693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155107812025955216353379795 232661718038932824530069693)
  ·
    refine ⟨87248144264599809198776135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232661718038932824530069693 87248144264599809198776135)
    ·
      refine ⟨130872216396899713798164203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87248144264599809198776135 130872216396899713798164203)
      ·
        refine ⟨196308324595349570697246305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130872216396899713798164203 196308324595349570697246305)
        ·
          refine ⟨147231243446512178022934729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196308324595349570697246305 147231243446512178022934729)
          ·
            refine ⟨110423432584884133517201047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147231243446512178022934729 110423432584884133517201047)
            ·
              refine ⟨165635148877326200275801571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110423432584884133517201047 165635148877326200275801571)
              ·
                refine ⟨248452723315989300413702357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165635148877326200275801571 248452723315989300413702357)
                ·
                  refine ⟨5823110702718499228446149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 248452723315989300413702357 5823110702718499228446149)
                  ·
                    refine ⟨1091833256759718605333653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5823110702718499228446149 1091833256759718605333653)
                    ·
                      rfl

theorem cell23_6379013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 4].length) (baseStart_6379013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379013 prefixEnd_6379013 := by exact prefixLift 6379013
  have htrace : WordTrace (prefixWord ++ tailWord_6379013) baseStart_6379013 baseEnd_6379013 := by
    simpa [prefixWord, tailWord_6379013, baseEnd_6379013] using wordTrace_append hprefix tailTrace_6379013
  have hstable : (prefixWord ++ tailWord_6379013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379013).length < 2 ^ (prefixWord ++ tailWord_6379013).sum := by decide
  have hdescent : baseEnd_6379013 < baseStart_6379013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379040 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 3]
def baseStart_6379040 : Nat := 118140960795 + 6379040 * 2 ^ 59
def prefixEnd_6379040 : Nat := 4983230072969 + 3 ^ 40 * 6379040 * 2
def baseEnd_6379040 : Nat := 3275513634256827210363335

theorem tailTrace_6379040 : CollatzResearch.WordTrace tailWord_6379040 prefixEnd_6379040 3275513634256827210363335 := by
  unfold tailWord_6379040
  simp only [CollatzResearch.WordTrace]
  refine ⟨116331351404917504070651287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155108468539890005427535049 116331351404917504070651287)
  ·
    refine ⟨174497027107376256105976931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116331351404917504070651287 174497027107376256105976931)
    ·
      refine ⟨261745540661064384158965397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174497027107376256105976931 261745540661064384158965397)
      ·
        refine ⟨12269322218487393007451503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 261745540661064384158965397 12269322218487393007451503)
        ·
          refine ⟨18403983327731089511177255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12269322218487393007451503 18403983327731089511177255)
          ·
            refine ⟨27605974991596634266765883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18403983327731089511177255 27605974991596634266765883)
            ·
              refine ⟨41408962487394951400148825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27605974991596634266765883 41408962487394951400148825)
              ·
                refine ⟨31056721865546213550111619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41408962487394951400148825 31056721865546213550111619)
                ·
                  refine ⟨46585082798319320325167429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31056721865546213550111619 46585082798319320325167429)
                  ·
                    refine ⟨8734703024684872560968893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46585082798319320325167429 8734703024684872560968893)
                    ·
                      refine ⟨3275513634256827210363335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8734703024684872560968893 3275513634256827210363335)
                      ·
                        rfl

theorem cell23_6379040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_6379040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379040 prefixEnd_6379040 := by exact prefixLift 6379040
  have htrace : WordTrace (prefixWord ++ tailWord_6379040) baseStart_6379040 baseEnd_6379040 := by
    simpa [prefixWord, tailWord_6379040, baseEnd_6379040] using wordTrace_append hprefix tailTrace_6379040
  have hstable : (prefixWord ++ tailWord_6379040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379040).length < 2 ^ (prefixWord ++ tailWord_6379040).sum := by decide
  have hdescent : baseEnd_6379040 < baseStart_6379040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379064 : List Nat := [2, 1, 2, 1, 4, 4, 1, 3, 1, 4]
def baseStart_6379064 : Nat := 118140960795 + 6379064 * 2 ^ 59
def prefixEnd_6379064 : Nat := 4983230072969 + 3 ^ 40 * 6379064 * 2
def baseEnd_6379064 : Nat := 1091841985930845038821075

theorem tailTrace_6379064 : CollatzResearch.WordTrace tailWord_6379064 prefixEnd_6379064 1091841985930845038821075 := by
  unfold tailWord_6379064
  simp only [CollatzResearch.WordTrace]
  refine ⟨116331789080874030120088123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155109052107832040160117497 116331789080874030120088123)
  ·
    refine ⟨174497683621311045180132185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116331789080874030120088123 174497683621311045180132185)
    ·
      refine ⟨130873262715983283885099139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174497683621311045180132185 130873262715983283885099139)
      ·
        refine ⟨196309894073974925827648709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130873262715983283885099139 196309894073974925827648709)
        ·
          refine ⟨36808105138870298592684133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196309894073974925827648709 36808105138870298592684133)
          ·
            refine ⟨6901519713538180986128275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36808105138870298592684133 6901519713538180986128275)
            ·
              refine ⟨10352279570307271479192413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6901519713538180986128275 10352279570307271479192413)
              ·
                refine ⟨3882104838865226804697155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10352279570307271479192413 3882104838865226804697155)
                ·
                  refine ⟨5823157258297840207045733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3882104838865226804697155 5823157258297840207045733)
                  ·
                    refine ⟨1091841985930845038821075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5823157258297840207045733 1091841985930845038821075)
                    ·
                      rfl

theorem cell23_6379064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 1, 4].length) (baseStart_6379064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379064 prefixEnd_6379064 := by exact prefixLift 6379064
  have htrace : WordTrace (prefixWord ++ tailWord_6379064) baseStart_6379064 baseEnd_6379064 := by
    simpa [prefixWord, tailWord_6379064, baseEnd_6379064] using wordTrace_append hprefix tailTrace_6379064
  have hstable : (prefixWord ++ tailWord_6379064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379064).length < 2 ^ (prefixWord ++ tailWord_6379064).sum := by decide
  have hdescent : baseEnd_6379064 < baseStart_6379064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379093 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_6379093 : Nat := 118140960795 + 6379093 * 2 ^ 59
def prefixEnd_6379093 : Nat := 4983230072969 + 3 ^ 40 * 6379093 * 2
def baseEnd_6379093 : Nat := 3275540848731515503000591

theorem tailTrace_6379093 : CollatzResearch.WordTrace tailWord_6379093 prefixEnd_6379093 3275540848731515503000591 := by
  unfold tailWord_6379093
  simp only [CollatzResearch.WordTrace]
  refine ⟨232664635878642998192981933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155109757252428665461987955 232664635878642998192981933)
  ·
    refine ⟨87249238454491124322368225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232664635878642998192981933 87249238454491124322368225)
    ·
      refine ⟨65436928840868343241776169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87249238454491124322368225 65436928840868343241776169)
      ·
        refine ⟨49077696630651257431332127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65436928840868343241776169 49077696630651257431332127)
        ·
          refine ⟨73616544945976886146998191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49077696630651257431332127 73616544945976886146998191)
          ·
            refine ⟨110424817418965329220497287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73616544945976886146998191 110424817418965329220497287)
            ·
              refine ⟨165637226128447993830745931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110424817418965329220497287 165637226128447993830745931)
              ·
                refine ⟨248455839192671990746118897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165637226128447993830745931 248455839192671990746118897)
                ·
                  refine ⟨186341879394503993059589173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248455839192671990746118897 186341879394503993059589173)
                  ·
                    refine ⟨17469551193234749349336485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 186341879394503993059589173 17469551193234749349336485)
                    ·
                      refine ⟨3275540848731515503000591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17469551193234749349336485 3275540848731515503000591)
                      ·
                        rfl

theorem cell23_6379093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_6379093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379093 prefixEnd_6379093 := by exact prefixLift 6379093
  have htrace : WordTrace (prefixWord ++ tailWord_6379093) baseStart_6379093 baseEnd_6379093 := by
    simpa [prefixWord, tailWord_6379093, baseEnd_6379093] using wordTrace_append hprefix tailTrace_6379093
  have hstable : (prefixWord ++ tailWord_6379093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379093).length < 2 ^ (prefixWord ++ tailWord_6379093).sum := by decide
  have hdescent : baseEnd_6379093 < baseStart_6379093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379107 : List Nat := [1, 1, 1, 5, 1, 5, 1, 2, 1, 5]
def baseStart_6379107 : Nat := 118140960795 + 6379107 * 2 ^ 59
def prefixEnd_6379107 : Nat := 4983230072969 + 3 ^ 40 * 6379107 * 2
def baseEnd_6379107 : Nat := 1091849345820226149408509

theorem tailTrace_6379107 : CollatzResearch.WordTrace tailWord_6379107 prefixEnd_6379107 1091849345820226149408509 := by
  unfold tailWord_6379107
  simp only [CollatzResearch.WordTrace]
  refine ⟨232665146500592278583991575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155110097667061519055994383 232665146500592278583991575)
  ·
    refine ⟨348997719750888417875987363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232665146500592278583991575 348997719750888417875987363)
    ·
      refine ⟨523496579626332626813981045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348997719750888417875987363 523496579626332626813981045)
      ·
        refine ⟨49077804339968683763810723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 523496579626332626813981045 49077804339968683763810723)
        ·
          refine ⟨73616706509953025645716085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49077804339968683763810723 73616706509953025645716085)
          ·
            refine ⟨6901566235308096154285883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73616706509953025645716085 6901566235308096154285883)
            ·
              refine ⟨10352349352962144231428825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6901566235308096154285883 10352349352962144231428825)
              ·
                refine ⟨7764262014721608173571619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10352349352962144231428825 7764262014721608173571619)
                ·
                  refine ⟨11646393022082412260357429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7764262014721608173571619 11646393022082412260357429)
                  ·
                    refine ⟨1091849345820226149408509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11646393022082412260357429 1091849345820226149408509)
                    ·
                      rfl

theorem cell23_6379107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 5].length) (baseStart_6379107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379107 prefixEnd_6379107 := by exact prefixLift 6379107
  have htrace : WordTrace (prefixWord ++ tailWord_6379107) baseStart_6379107 baseEnd_6379107 := by
    simpa [prefixWord, tailWord_6379107, baseEnd_6379107] using wordTrace_append hprefix tailTrace_6379107
  have hstable : (prefixWord ++ tailWord_6379107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379107).length < 2 ^ (prefixWord ++ tailWord_6379107).sum := by decide
  have hdescent : baseEnd_6379107 < baseStart_6379107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379113 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 3, 1, 5]
def baseStart_6379113 : Nat := 118140960795 + 6379113 * 2 ^ 59
def prefixEnd_6379113 : Nat := 4983230072969 + 3 ^ 40 * 6379113 * 2
def baseEnd_6379113 : Nat := 3275551118344605424750499

theorem tailTrace_6379113 : CollatzResearch.WordTrace tailWord_6379113 prefixEnd_6379113 3275551118344605424750499 := by
  unfold tailWord_6379113
  simp only [CollatzResearch.WordTrace]
  refine ⟨232665365338570541608709993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155110243559047027739139995 232665365338570541608709993)
  ·
    refine ⟨174499024003927906206532495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232665365338570541608709993 174499024003927906206532495)
    ·
      refine ⟨261748536005891859309798743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174499024003927906206532495 261748536005891859309798743)
      ·
        refine ⟨392622804008837788964698115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261748536005891859309798743 392622804008837788964698115)
        ·
          refine ⟨588934206013256683447047173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392622804008837788964698115 588934206013256683447047173)
          ·
            refine ⟨110425163627485628146321345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 588934206013256683447047173 110425163627485628146321345)
            ·
              refine ⟨82818872720614221109741009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110425163627485628146321345 82818872720614221109741009)
              ·
                refine ⟨62114154540460665832305757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82818872720614221109741009 62114154540460665832305757)
                ·
                  refine ⟨23292807952672749687114659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62114154540460665832305757 23292807952672749687114659)
                  ·
                    refine ⟨34939211929009124530671989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23292807952672749687114659 34939211929009124530671989)
                    ·
                      refine ⟨3275551118344605424750499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34939211929009124530671989 3275551118344605424750499)
                      ·
                        rfl

theorem cell23_6379113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 1, 5].length) (baseStart_6379113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379113 prefixEnd_6379113 := by exact prefixLift 6379113
  have htrace : WordTrace (prefixWord ++ tailWord_6379113) baseStart_6379113 baseEnd_6379113 := by
    simpa [prefixWord, tailWord_6379113, baseEnd_6379113] using wordTrace_append hprefix tailTrace_6379113
  have hstable : (prefixWord ++ tailWord_6379113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379113).length < 2 ^ (prefixWord ++ tailWord_6379113).sum := by decide
  have hdescent : baseEnd_6379113 < baseStart_6379113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379114 : List Nat := [3, 1, 3, 2, 1, 3, 2, 1, 2, 3, 2]
def baseStart_6379114 : Nat := 118140960795 + 6379114 * 2 ^ 59
def prefixEnd_6379114 : Nat := 4983230072969 + 3 ^ 40 * 6379114 * 2
def baseEnd_6379114 : Nat := 3275551631825259920837995

theorem tailTrace_6379114 : CollatzResearch.WordTrace tailWord_6379114 prefixEnd_6379114 3275551631825259920837995 := by
  unfold tailWord_6379114
  simp only [CollatzResearch.WordTrace]
  refine ⟨58166350452891729694874099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155110267874377945852997597 58166350452891729694874099)
  ·
    refine ⟨87249525679337594542311149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58166350452891729694874099 87249525679337594542311149)
    ·
      refine ⟨32718572129751597953366681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87249525679337594542311149 32718572129751597953366681)
      ·
        refine ⟨24538929097313698465025011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32718572129751597953366681 24538929097313698465025011)
        ·
          refine ⟨36808393645970547697537517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24538929097313698465025011 36808393645970547697537517)
          ·
            refine ⟨13803147617238955386576569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36808393645970547697537517 13803147617238955386576569)
            ·
              refine ⟨10352360712929216539932427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13803147617238955386576569 10352360712929216539932427)
              ·
                refine ⟨15528541069393824809898641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10352360712929216539932427 15528541069393824809898641)
                ·
                  refine ⟨11646405802045368607423981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15528541069393824809898641 11646405802045368607423981)
                  ·
                    refine ⟨4367402175767013227783993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11646405802045368607423981 4367402175767013227783993)
                    ·
                      refine ⟨3275551631825259920837995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4367402175767013227783993 3275551631825259920837995)
                      ·
                        rfl

theorem cell23_6379114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_6379114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379114 prefixEnd_6379114 := by exact prefixLift 6379114
  have htrace : WordTrace (prefixWord ++ tailWord_6379114) baseStart_6379114 baseEnd_6379114 := by
    simpa [prefixWord, tailWord_6379114, baseEnd_6379114] using wordTrace_append hprefix tailTrace_6379114
  have hstable : (prefixWord ++ tailWord_6379114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379114).length < 2 ^ (prefixWord ++ tailWord_6379114).sum := by decide
  have hdescent : baseEnd_6379114 < baseStart_6379114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379120 : List Nat := [2, 1, 1, 1, 6, 2, 1, 2, 1, 6]
def baseStart_6379120 : Nat := 118140960795 + 6379120 * 2 ^ 59
def prefixEnd_6379120 : Nat := 4983230072969 + 3 ^ 40 * 6379120 * 2
def baseEnd_6379120 : Nat := 1091851570903062299120989

theorem tailTrace_6379120 : CollatzResearch.WordTrace tailWord_6379120 prefixEnd_6379120 1091851570903062299120989 := by
  unfold tailWord_6379120
  simp only [CollatzResearch.WordTrace]
  refine ⟨116332810324772590902107407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155110413766363454536143209 116332810324772590902107407)
  ·
    refine ⟨174499215487158886353161111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116332810324772590902107407 174499215487158886353161111)
    ·
      refine ⟨261748823230738329529741667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174499215487158886353161111 261748823230738329529741667)
      ·
        refine ⟨392623234846107494294612501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261748823230738329529741667 392623234846107494294612501)
        ·
          refine ⟨18404214133411288795059961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 392623234846107494294612501 18404214133411288795059961)
          ·
            refine ⟨13803160600058466596294971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18404214133411288795059961 13803160600058466596294971)
            ·
              refine ⟨20704740900087699894442457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13803160600058466596294971 20704740900087699894442457)
              ·
                refine ⟨15528555675065774920831843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20704740900087699894442457 15528555675065774920831843)
                ·
                  refine ⟨23292833512598662381247765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15528555675065774920831843 23292833512598662381247765)
                  ·
                    refine ⟨1091851570903062299120989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23292833512598662381247765 1091851570903062299120989)
                    ·
                      rfl

theorem cell23_6379120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 1, 6].length) (baseStart_6379120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379120 prefixEnd_6379120 := by exact prefixLift 6379120
  have htrace : WordTrace (prefixWord ++ tailWord_6379120) baseStart_6379120 baseEnd_6379120 := by
    simpa [prefixWord, tailWord_6379120, baseEnd_6379120] using wordTrace_append hprefix tailTrace_6379120
  have hstable : (prefixWord ++ tailWord_6379120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379120).length < 2 ^ (prefixWord ++ tailWord_6379120).sum := by decide
  have hdescent : baseEnd_6379120 < baseStart_6379120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379133 : List Nat := [1, 4, 1, 1, 4, 12]
def baseStart_6379133 : Nat := 118140960795 + 6379133 * 2 ^ 59
def prefixEnd_6379133 : Nat := 4983230072969 + 3 ^ 40 * 6379133 * 2
def baseEnd_6379133 : Nat := 13479676493653067269549

theorem tailTrace_6379133 : CollatzResearch.WordTrace tailWord_6379133 prefixEnd_6379133 13479676493653067269549 := by
  unfold tailWord_6379133
  simp only [CollatzResearch.WordTrace]
  refine ⟨232666094798498085024438053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155110729865665390016292035 232666094798498085024438053)
  ·
    refine ⟨43624892774718390942082135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232666094798498085024438053 43624892774718390942082135)
    ·
      refine ⟨65437339162077586413123203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43624892774718390942082135 65437339162077586413123203)
      ·
        refine ⟨98156008743116379619684805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65437339162077586413123203 98156008743116379619684805)
        ·
          refine ⟨18404251639334321178690901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98156008743116379619684805 18404251639334321178690901)
          ·
            refine ⟨13479676493653067269549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 18404251639334321178690901 13479676493653067269549)
            ·
              rfl

theorem cell23_6379133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 12].length) (baseStart_6379133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379133 prefixEnd_6379133 := by exact prefixLift 6379133
  have htrace : WordTrace (prefixWord ++ tailWord_6379133) baseStart_6379133 baseEnd_6379133 := by
    simpa [prefixWord, tailWord_6379133, baseEnd_6379133] using wordTrace_append hprefix tailTrace_6379133
  have hstable : (prefixWord ++ tailWord_6379133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379133).length < 2 ^ (prefixWord ++ tailWord_6379133).sum := by decide
  have hdescent : baseEnd_6379133 < baseStart_6379133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379137 : List Nat := [1, 2, 4, 2, 1, 2, 1, 4, 2, 4]
def baseStart_6379137 : Nat := 118140960795 + 6379137 * 2 ^ 59
def prefixEnd_6379137 : Nat := 4983230072969 + 3 ^ 40 * 6379137 * 2
def baseEnd_6379137 : Nat := 1091854480626771110283463

theorem tailTrace_6379137 : CollatzResearch.WordTrace tailWord_6379137 prefixEnd_6379137 1091854480626771110283463 := by
  unfold tailWord_6379137
  simp only [CollatzResearch.WordTrace]
  refine ⟨232666240690483593707583665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155110827126989062471722443 232666240690483593707583665)
  ·
    refine ⟨174499680517862695280687749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232666240690483593707583665 174499680517862695280687749)
    ·
      refine ⟨32718690097099255365128953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174499680517862695280687749 32718690097099255365128953)
      ·
        refine ⟨24539017572824441523846715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32718690097099255365128953 24539017572824441523846715)
        ·
          refine ⟨36808526359236662285770073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24539017572824441523846715 36808526359236662285770073)
          ·
            refine ⟨27606394769427496714327555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36808526359236662285770073 27606394769427496714327555)
            ·
              refine ⟨41409592154141245071491333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27606394769427496714327555 41409592154141245071491333)
              ·
                refine ⟨7764298528901483450904625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41409592154141245071491333 7764298528901483450904625)
                ·
                  refine ⟨5823223896676112588178469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7764298528901483450904625 5823223896676112588178469)
                  ·
                    refine ⟨1091854480626771110283463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5823223896676112588178469 1091854480626771110283463)
                    ·
                      rfl

theorem cell23_6379137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_6379137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379137 prefixEnd_6379137 := by exact prefixLift 6379137
  have htrace : WordTrace (prefixWord ++ tailWord_6379137) baseStart_6379137 baseEnd_6379137 := by
    simpa [prefixWord, tailWord_6379137, baseEnd_6379137] using wordTrace_append hprefix tailTrace_6379137
  have hstable : (prefixWord ++ tailWord_6379137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379137).length < 2 ^ (prefixWord ++ tailWord_6379137).sum := by decide
  have hdescent : baseEnd_6379137 < baseStart_6379137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379150 : List Nat := [4, 1, 1, 3, 1, 2, 3, 8]
def baseStart_6379150 : Nat := 118140960795 + 6379150 * 2 ^ 59
def prefixEnd_6379150 : Nat := 4983230072969 + 3 ^ 40 * 6379150 * 2
def baseEnd_6379150 : Nat := 121317411745511917777327

theorem tailTrace_6379150 : CollatzResearch.WordTrace tailWord_6379150 prefixEnd_6379150 121317411745511917777327 := by
  unfold tailWord_6379150
  simp only [CollatzResearch.WordTrace]
  refine ⟨29083339354929562115975863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155111143226290997951871269 29083339354929562115975863)
  ·
    refine ⟨43625009032394343173963795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29083339354929562115975863 43625009032394343173963795)
    ·
      refine ⟨65437513548591514760945693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43625009032394343173963795 65437513548591514760945693)
      ·
        refine ⟨24539067580721818035354635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65437513548591514760945693 24539067580721818035354635)
        ·
          refine ⟨36808601371082727053031953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24539067580721818035354635 36808601371082727053031953)
          ·
            refine ⟨27606451028312045289773965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36808601371082727053031953 27606451028312045289773965)
            ·
              refine ⟨10352419135617016983665237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27606451028312045289773965 10352419135617016983665237)
              ·
                refine ⟨121317411745511917777327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10352419135617016983665237 121317411745511917777327)
                ·
                  rfl

theorem cell23_6379150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 8].length) (baseStart_6379150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379150 prefixEnd_6379150 := by exact prefixLift 6379150
  have htrace : WordTrace (prefixWord ++ tailWord_6379150) baseStart_6379150 baseEnd_6379150 := by
    simpa [prefixWord, tailWord_6379150, baseEnd_6379150] using wordTrace_append hprefix tailTrace_6379150
  have hstable : (prefixWord ++ tailWord_6379150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379150).length < 2 ^ (prefixWord ++ tailWord_6379150).sum := by decide
  have hdescent : baseEnd_6379150 < baseStart_6379150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379194 : List Nat := [3, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3]
def baseStart_6379194 : Nat := 118140960795 + 6379194 * 2 ^ 59
def prefixEnd_6379194 : Nat := 4983230072969 + 3 ^ 40 * 6379194 * 2
def baseEnd_6379194 : Nat := 3275592710277619607837627

theorem tailTrace_6379194 : CollatzResearch.WordTrace tailWord_6379194 prefixEnd_6379194 3275592710277619607837627 := by
  unfold tailWord_6379194
  simp only [CollatzResearch.WordTrace]
  refine ⟨58167079912819273110602159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155112213100851394961605757 58167079912819273110602159)
  ·
    refine ⟨87250619869228909665903239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58167079912819273110602159 87250619869228909665903239)
    ·
      refine ⟨130875929803843364498854859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87250619869228909665903239 130875929803843364498854859)
      ·
        refine ⟨196313894705765046748282289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130875929803843364498854859 196313894705765046748282289)
        ·
          refine ⟨147235421029323785061211717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196313894705765046748282289 147235421029323785061211717)
          ·
            refine ⟨27606641442998209698977197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147235421029323785061211717 27606641442998209698977197)
            ·
              refine ⟨10352490541124328637116449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27606641442998209698977197 10352490541124328637116449)
              ·
                refine ⟨7764367905843246477837337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10352490541124328637116449 7764367905843246477837337)
                ·
                  refine ⟨5823275929382434858378003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7764367905843246477837337 5823275929382434858378003)
                  ·
                    refine ⟨8734913894073652287567005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5823275929382434858378003 8734913894073652287567005)
                    ·
                      refine ⟨3275592710277619607837627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8734913894073652287567005 3275592710277619607837627)
                      ·
                        rfl

theorem cell23_6379194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3].length) (baseStart_6379194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379194 prefixEnd_6379194 := by exact prefixLift 6379194
  have htrace : WordTrace (prefixWord ++ tailWord_6379194) baseStart_6379194 baseEnd_6379194 := by
    simpa [prefixWord, tailWord_6379194, baseEnd_6379194] using wordTrace_append hprefix tailTrace_6379194
  have hstable : (prefixWord ++ tailWord_6379194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379194).length < 2 ^ (prefixWord ++ tailWord_6379194).sum := by decide
  have hdescent : baseEnd_6379194 < baseStart_6379194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379250 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_6379250 : Nat := 118140960795 + 6379250 * 2 ^ 59
def prefixEnd_6379250 : Nat := 4983230072969 + 3 ^ 40 * 6379250 * 2
def baseEnd_6379250 : Nat := 3275621465194271388737369

theorem tailTrace_6379250 : CollatzResearch.WordTrace tailWord_6379250 prefixEnd_6379250 3275621465194271388737369 := by
  unfold tailWord_6379250
  simp only [CollatzResearch.WordTrace]
  refine ⟨58167590534768553501611801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155113574759382809337631469 58167590534768553501611801)
  ·
    refine ⟨43625692901076415126208851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58167590534768553501611801 43625692901076415126208851)
    ·
      refine ⟨65438539351614622689313277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43625692901076415126208851 65438539351614622689313277)
      ·
        refine ⟨24539452256855483508492479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65438539351614622689313277 24539452256855483508492479)
        ·
          refine ⟨36809178385283225262738719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24539452256855483508492479 36809178385283225262738719)
          ·
            refine ⟨55213767577924837894108079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36809178385283225262738719 55213767577924837894108079)
            ·
              refine ⟨82820651366887256841162119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55213767577924837894108079 82820651366887256841162119)
              ·
                refine ⟨124230977050330885261743179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82820651366887256841162119 124230977050330885261743179)
                ·
                  refine ⟨186346465575496327892614769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124230977050330885261743179 186346465575496327892614769)
                  ·
                    refine ⟨139759849181622245919461077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 186346465575496327892614769 139759849181622245919461077)
                    ·
                      refine ⟨3275621465194271388737369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139759849181622245919461077 3275621465194271388737369)
                      ·
                        rfl

theorem cell23_6379250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_6379250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379250 prefixEnd_6379250 := by exact prefixLift 6379250
  have htrace : WordTrace (prefixWord ++ tailWord_6379250) baseStart_6379250 baseEnd_6379250 := by
    simpa [prefixWord, tailWord_6379250, baseEnd_6379250] using wordTrace_append hprefix tailTrace_6379250
  have hstable : (prefixWord ++ tailWord_6379250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379250).length < 2 ^ (prefixWord ++ tailWord_6379250).sum := by decide
  have hdescent : baseEnd_6379250 < baseStart_6379250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379268 : List Nat := [2, 3, 2, 2, 1, 2, 4, 1, 2, 2, 2]
def baseStart_6379268 : Nat := 118140960795 + 6379268 * 2 ^ 59
def prefixEnd_6379268 : Nat := 4983230072969 + 3 ^ 40 * 6379268 * 2
def baseEnd_6379268 : Nat := 3275630707846052318312287

theorem tailTrace_6379268 : CollatzResearch.WordTrace tailWord_6379268 prefixEnd_6379268 3275630707846052318312287 := by
  unfold tailWord_6379268
  simp only [CollatzResearch.WordTrace]
  refine ⟨116335509326504501540301229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155114012435339335387068305 116335509326504501540301229)
  ·
    refine ⟨43625815997439188077612961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116335509326504501540301229 43625815997439188077612961)
    ·
      refine ⟨32719361998079391058209721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43625815997439188077612961 32719361998079391058209721)
      ·
        refine ⟨24539521498559543293657291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32719361998079391058209721 24539521498559543293657291)
        ·
          refine ⟨36809282247839314940485937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24539521498559543293657291 36809282247839314940485937)
          ·
            refine ⟨27606961685879486205364453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36809282247839314940485937 27606961685879486205364453)
            ·
              refine ⟨5176305316102403663505835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27606961685879486205364453 5176305316102403663505835)
              ·
                refine ⟨7764457974153605495258753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5176305316102403663505835 7764457974153605495258753)
                ·
                  refine ⟨5823343480615204121444065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7764457974153605495258753 5823343480615204121444065)
                  ·
                    refine ⟨4367507610461403091083049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5823343480615204121444065 4367507610461403091083049)
                    ·
                      refine ⟨3275630707846052318312287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4367507610461403091083049 3275630707846052318312287)
                      ·
                        rfl

theorem cell23_6379268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_6379268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379268 prefixEnd_6379268 := by exact prefixLift 6379268
  have htrace : WordTrace (prefixWord ++ tailWord_6379268) baseStart_6379268 baseEnd_6379268 := by
    simpa [prefixWord, tailWord_6379268, baseEnd_6379268] using wordTrace_append hprefix tailTrace_6379268
  have hstable : (prefixWord ++ tailWord_6379268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379268).length < 2 ^ (prefixWord ++ tailWord_6379268).sum := by decide
  have hdescent : baseEnd_6379268 < baseStart_6379268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379287 : List Nat := [1, 1, 3, 4, 2, 1, 1, 3, 2, 5]
def baseStart_6379287 : Nat := 118140960795 + 6379287 * 2 ^ 59
def prefixEnd_6379287 : Nat := 4983230072969 + 3 ^ 40 * 6379287 * 2
def baseEnd_6379287 : Nat := 1091880154659495914658233

theorem tailTrace_6379287 : CollatzResearch.WordTrace tailWord_6379287 prefixEnd_6379287 1091880154659495914658233 := by
  unfold tailWord_6379287
  simp only [CollatzResearch.WordTrace]
  refine ⟨232671711639940169325544115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155114474426626779550362743 232671711639940169325544115)
  ·
    refine ⟨349007567459910253988316173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232671711639940169325544115 349007567459910253988316173)
    ·
      refine ⟨130877837797466345245618565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349007567459910253988316173 130877837797466345245618565)
      ·
        refine ⟨24539594587024939733553481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130877837797466345245618565 24539594587024939733553481)
        ·
          refine ⟨18404695940268704800165111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24539594587024939733553481 18404695940268704800165111)
          ·
            refine ⟨27607043910403057200247667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18404695940268704800165111 27607043910403057200247667)
            ·
              refine ⟨41410565865604585800371501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27607043910403057200247667 41410565865604585800371501)
              ·
                refine ⟨15528962199601719675139313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41410565865604585800371501 15528962199601719675139313)
                ·
                  refine ⟨11646721649701289756354485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15528962199601719675139313 11646721649701289756354485)
                  ·
                    refine ⟨1091880154659495914658233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11646721649701289756354485 1091880154659495914658233)
                    ·
                      rfl

theorem cell23_6379287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_6379287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379287 prefixEnd_6379287 := by exact prefixLift 6379287
  have htrace : WordTrace (prefixWord ++ tailWord_6379287) baseStart_6379287 baseEnd_6379287 := by
    simpa [prefixWord, tailWord_6379287, baseEnd_6379287] using wordTrace_append hprefix tailTrace_6379287
  have hstable : (prefixWord ++ tailWord_6379287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379287).length < 2 ^ (prefixWord ++ tailWord_6379287).sum := by decide
  have hdescent : baseEnd_6379287 < baseStart_6379287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379341 : List Nat := [1, 6, 1, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_6379341 : Nat := 118140960795 + 6379341 * 2 ^ 59
def prefixEnd_6379341 : Nat := 4983230072969 + 3 ^ 40 * 6379341 * 2
def baseEnd_6379341 : Nat := 3275668191933830532699451

theorem tailTrace_6379341 : CollatzResearch.WordTrace tailWord_6379341 prefixEnd_6379341 3275668191933830532699451 := by
  unfold tailWord_6379341
  simp only [CollatzResearch.WordTrace]
  refine ⟨232673681181744536548009877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155115787454496357698673251 232673681181744536548009877)
  ·
    refine ⟨10906578805394275150687963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 232673681181744536548009877 10906578805394275150687963)
    ·
      refine ⟨16359868208091412726031945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10906578805394275150687963 16359868208091412726031945)
      ·
        refine ⟨12269901156068559544523959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16359868208091412726031945 12269901156068559544523959)
        ·
          refine ⟨18404851734102839316785939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12269901156068559544523959 18404851734102839316785939)
          ·
            refine ⟨27607277601154258975178909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18404851734102839316785939 27607277601154258975178909)
            ·
              refine ⟨10352729100432847115692091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27607277601154258975178909 10352729100432847115692091)
              ·
                refine ⟨15529093650649270673538137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10352729100432847115692091 15529093650649270673538137)
                ·
                  refine ⟨11646820237986953005153603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15529093650649270673538137 11646820237986953005153603)
                  ·
                    refine ⟨17470230356980429507730405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11646820237986953005153603 17470230356980429507730405)
                    ·
                      refine ⟨3275668191933830532699451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17470230356980429507730405 3275668191933830532699451)
                      ·
                        rfl

theorem cell23_6379341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_6379341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379341 prefixEnd_6379341 := by exact prefixLift 6379341
  have htrace : WordTrace (prefixWord ++ tailWord_6379341) baseStart_6379341 baseEnd_6379341 := by
    simpa [prefixWord, tailWord_6379341, baseEnd_6379341] using wordTrace_append hprefix tailTrace_6379341
  have hstable : (prefixWord ++ tailWord_6379341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379341).length < 2 ^ (prefixWord ++ tailWord_6379341).sum := by decide
  have hdescent : baseEnd_6379341 < baseStart_6379341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379417 : List Nat := [1, 2, 1, 2, 1, 3, 3, 3, 1, 1, 5]
def baseStart_6379417 : Nat := 118140960795 + 6379417 * 2 ^ 59
def prefixEnd_6379417 : Nat := 4983230072969 + 3 ^ 40 * 6379417 * 2
def baseEnd_6379417 : Nat := 3275707216463572235349101

theorem tailTrace_6379417 : CollatzResearch.WordTrace tailWord_6379417 prefixEnd_6379417 3275707216463572235349101 := by
  unfold tailWord_6379417
  simp only [CollatzResearch.WordTrace]
  refine ⟨232676453129469201527776505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155117635419646134351851003 232676453129469201527776505)
  ·
    refine ⟨174507339847101901145832379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232676453129469201527776505 174507339847101901145832379)
    ·
      refine ⟨261761009770652851718748569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174507339847101901145832379 261761009770652851718748569)
      ·
        refine ⟨196320757327989638789061427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261761009770652851718748569 196320757327989638789061427)
        ·
          refine ⟨294481135991984458183592141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196320757327989638789061427 294481135991984458183592141)
          ·
            refine ⟨110430425996994171818847053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294481135991984458183592141 110430425996994171818847053)
            ·
              refine ⟨41411409748872814432067645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110430425996994171818847053 41411409748872814432067645)
              ·
                refine ⟨15529278655827305412025367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41411409748872814432067645 15529278655827305412025367)
                ·
                  refine ⟨23293917983740958118038051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15529278655827305412025367 23293917983740958118038051)
                  ·
                    refine ⟨34940876975611437177057077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23293917983740958118038051 34940876975611437177057077)
                    ·
                      refine ⟨3275707216463572235349101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34940876975611437177057077 3275707216463572235349101)
                      ·
                        rfl

theorem cell23_6379417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_6379417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379417 prefixEnd_6379417 := by exact prefixLift 6379417
  have htrace : WordTrace (prefixWord ++ tailWord_6379417) baseStart_6379417 baseEnd_6379417 := by
    simpa [prefixWord, tailWord_6379417, baseEnd_6379417] using wordTrace_append hprefix tailTrace_6379417
  have hstable : (prefixWord ++ tailWord_6379417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379417).length < 2 ^ (prefixWord ++ tailWord_6379417).sum := by decide
  have hdescent : baseEnd_6379417 < baseStart_6379417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379424 : List Nat := [2, 1, 1, 4, 1, 1, 1, 6, 2, 4]
def baseStart_6379424 : Nat := 118140960795 + 6379424 * 2 ^ 59
def prefixEnd_6379424 : Nat := 4983230072969 + 3 ^ 40 * 6379424 * 2
def baseEnd_6379424 : Nat := 1091903603609384569320523

theorem tailTrace_6379424 : CollatzResearch.WordTrace tailWord_6379424 prefixEnd_6379424 1091903603609384569320523 := by
  unfold tailWord_6379424
  simp only [CollatzResearch.WordTrace]
  refine ⟨116338354220221920861640663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155117805626962561148854217 116338354220221920861640663)
  ·
    refine ⟨174507531330332881292460995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116338354220221920861640663 174507531330332881292460995)
    ·
      refine ⟨261761296995499321938691493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174507531330332881292460995 261761296995499321938691493)
      ·
        refine ⟨49080243186656122863504655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261761296995499321938691493 49080243186656122863504655)
        ·
          refine ⟨73620364779984184295256983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49080243186656122863504655 73620364779984184295256983)
          ·
            refine ⟨110430547169976276442885475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73620364779984184295256983 110430547169976276442885475)
            ·
              refine ⟨165645820754964414664328213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110430547169976276442885475 165645820754964414664328213)
              ·
                refine ⟨7764647847888956937390385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 165645820754964414664328213 7764647847888956937390385)
                ·
                  refine ⟨5823485885916717703042789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7764647847888956937390385 5823485885916717703042789)
                  ·
                    refine ⟨1091903603609384569320523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5823485885916717703042789 1091903603609384569320523)
                    ·
                      rfl

theorem cell23_6379424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 2, 4].length) (baseStart_6379424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379424 prefixEnd_6379424 := by exact prefixLift 6379424
  have htrace : WordTrace (prefixWord ++ tailWord_6379424) baseStart_6379424 baseEnd_6379424 := by
    simpa [prefixWord, tailWord_6379424, baseEnd_6379424] using wordTrace_append hprefix tailTrace_6379424
  have hstable : (prefixWord ++ tailWord_6379424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379424).length < 2 ^ (prefixWord ++ tailWord_6379424).sum := by decide
  have hdescent : baseEnd_6379424 < baseStart_6379424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379425 : List Nat := [1, 2, 3, 4, 3, 1, 1, 1, 3, 1, 3]
def baseStart_6379425 : Nat := 118140960795 + 6379425 * 2 ^ 59
def prefixEnd_6379425 : Nat := 4983230072969 + 3 ^ 40 * 6379425 * 2
def baseEnd_6379425 : Nat := 3275711324308808204049065

theorem tailTrace_6379425 : CollatzResearch.WordTrace tailWord_6379425 prefixEnd_6379425 3275711324308808204049065 := by
  unfold tailWord_6379425
  simp only [CollatzResearch.WordTrace]
  refine ⟨232676744913440218894067729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155117829942293479262711819 232676744913440218894067729)
  ·
    refine ⟨174507558685080164170550797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232676744913440218894067729 174507558685080164170550797)
    ·
      refine ⟨65440334506905061563956549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174507558685080164170550797 65440334506905061563956549)
      ·
        refine ⟨12270062720044699043241853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65440334506905061563956549 12270062720044699043241853)
        ·
          refine ⟨4601273520016762141215695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12270062720044699043241853 4601273520016762141215695)
          ·
            refine ⟨6901910280025143211823543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4601273520016762141215695 6901910280025143211823543)
            ·
              refine ⟨10352865420037714817735315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6901910280025143211823543 10352865420037714817735315)
              ·
                refine ⟨15529298130056572226602973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10352865420037714817735315 15529298130056572226602973)
                ·
                  refine ⟨5823486798771214584976115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15529298130056572226602973 5823486798771214584976115)
                  ·
                    refine ⟨8735230198156821877464173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5823486798771214584976115 8735230198156821877464173)
                    ·
                      refine ⟨3275711324308808204049065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8735230198156821877464173 3275711324308808204049065)
                      ·
                        rfl

theorem cell23_6379425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_6379425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379425 prefixEnd_6379425 := by exact prefixLift 6379425
  have htrace : WordTrace (prefixWord ++ tailWord_6379425) baseStart_6379425 baseEnd_6379425 := by
    simpa [prefixWord, tailWord_6379425, baseEnd_6379425] using wordTrace_append hprefix tailTrace_6379425
  have hstable : (prefixWord ++ tailWord_6379425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379425).length < 2 ^ (prefixWord ++ tailWord_6379425).sum := by decide
  have hdescent : baseEnd_6379425 < baseStart_6379425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379441 : List Nat := [1, 2, 2, 4, 2, 2, 1, 3, 2, 4]
def baseStart_6379441 : Nat := 118140960795 + 6379441 * 2 ^ 59
def prefixEnd_6379441 : Nat := 4983230072969 + 3 ^ 40 * 6379441 * 2
def baseEnd_6379441 : Nat := 1091906513333093380482997

theorem tailTrace_6379441 : CollatzResearch.WordTrace tailWord_6379441 prefixEnd_6379441 1091906513333093380482997 := by
  unfold tailWord_6379441
  simp only [CollatzResearch.WordTrace]
  refine ⟨232677328481382253626650177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155118218987588169084433451 232677328481382253626650177)
  ·
    refine ⟨174507996361036690219987633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232677328481382253626650177 174507996361036690219987633)
    ·
      refine ⟨130880997270777517664990725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174507996361036690219987633 130880997270777517664990725)
      ·
        refine ⟨24540186988270784562185761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130880997270777517664990725 24540186988270784562185761)
        ·
          refine ⟨18405140241203088421639321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24540186988270784562185761 18405140241203088421639321)
          ·
            refine ⟨13803855180902316316229491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18405140241203088421639321 13803855180902316316229491)
            ·
              refine ⟨20705782771353474474344237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13803855180902316316229491 20705782771353474474344237)
              ·
                refine ⟨7764668539257552927879089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20705782771353474474344237 7764668539257552927879089)
                ·
                  refine ⟨5823501404443164695909317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7764668539257552927879089 5823501404443164695909317)
                  ·
                    refine ⟨1091906513333093380482997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5823501404443164695909317 1091906513333093380482997)
                    ·
                      rfl

theorem cell23_6379441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 4].length) (baseStart_6379441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379441 prefixEnd_6379441 := by exact prefixLift 6379441
  have htrace : WordTrace (prefixWord ++ tailWord_6379441) baseStart_6379441 baseEnd_6379441 := by
    simpa [prefixWord, tailWord_6379441, baseEnd_6379441] using wordTrace_append hprefix tailTrace_6379441
  have hstable : (prefixWord ++ tailWord_6379441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379441).length < 2 ^ (prefixWord ++ tailWord_6379441).sum := by decide
  have hdescent : baseEnd_6379441 < baseStart_6379441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379464 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 3, 3, 3]
def baseStart_6379464 : Nat := 118140960795 + 6379464 * 2 ^ 59
def prefixEnd_6379464 : Nat := 4983230072969 + 3 ^ 40 * 6379464 * 2
def baseEnd_6379464 : Nat := 3275731350054333551461385

theorem tailTrace_6379464 : CollatzResearch.WordTrace tailWord_6379464 prefixEnd_6379464 3275731350054333551461385 := by
  unfold tailWord_6379464
  simp only [CollatzResearch.WordTrace]
  refine ⟨116339083680149464277368723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155118778240199285703158297 116339083680149464277368723)
  ·
    refine ⟨174508625520224196416053085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116339083680149464277368723 174508625520224196416053085)
    ·
      refine ⟨65440734570084073656019907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174508625520224196416053085 65440734570084073656019907)
      ·
        refine ⟨98161101855126110484029861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65440734570084073656019907 98161101855126110484029861)
        ·
          refine ⟨18405206597836145715755599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98161101855126110484029861 18405206597836145715755599)
          ·
            refine ⟨27607809896754218573633399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18405206597836145715755599 27607809896754218573633399)
            ·
              refine ⟨41411714845131327860450099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27607809896754218573633399 41411714845131327860450099)
              ·
                refine ⟨62117572267696991790675149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41411714845131327860450099 62117572267696991790675149)
                ·
                  refine ⟨23294089600386371921503181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62117572267696991790675149 23294089600386371921503181)
                  ·
                    refine ⟨8735283600144889470563693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23294089600386371921503181 8735283600144889470563693)
                    ·
                      refine ⟨3275731350054333551461385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8735283600144889470563693 3275731350054333551461385)
                      ·
                        rfl

theorem cell23_6379464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_6379464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379464 prefixEnd_6379464 := by exact prefixLift 6379464
  have htrace : WordTrace (prefixWord ++ tailWord_6379464) baseStart_6379464 baseEnd_6379464 := by
    simpa [prefixWord, tailWord_6379464, baseEnd_6379464] using wordTrace_append hprefix tailTrace_6379464
  have hstable : (prefixWord ++ tailWord_6379464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379464).length < 2 ^ (prefixWord ++ tailWord_6379464).sum := by decide
  have hdescent : baseEnd_6379464 < baseStart_6379464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379468 : List Nat := [2, 2, 1, 4, 1, 3, 3, 1, 1, 2, 3]
def baseStart_6379468 : Nat := 118140960795 + 6379468 * 2 ^ 59
def prefixEnd_6379468 : Nat := 4983230072969 + 3 ^ 40 * 6379468 * 2
def baseEnd_6379468 : Nat := 3275733403976951535811367

theorem tailTrace_6379468 : CollatzResearch.WordTrace tailWord_6379468 prefixEnd_6379468 3275733403976951535811367 := by
  unfold tailWord_6379468
  simp only [CollatzResearch.WordTrace]
  refine ⟨116339156626142218618941529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155118875501522958158588705 116339156626142218618941529)
  ·
    refine ⟨87254367469606663964206147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116339156626142218618941529 87254367469606663964206147)
    ·
      refine ⟨130881551204409995946309221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87254367469606663964206147 130881551204409995946309221)
      ·
        refine ⟨24540290850826874239932979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130881551204409995946309221 24540290850826874239932979)
        ·
          refine ⟨36810436276240311359899469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24540290850826874239932979 36810436276240311359899469)
          ·
            refine ⟨13803913603590116759962301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36810436276240311359899469 13803913603590116759962301)
            ·
              refine ⟨5176467601346293784985863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13803913603590116759962301 5176467601346293784985863)
              ·
                refine ⟨7764701402019440677478795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5176467601346293784985863 7764701402019440677478795)
                ·
                  refine ⟨11647052103029161016218193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7764701402019440677478795 11647052103029161016218193)
                  ·
                    refine ⟨8735289077271870762163645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11647052103029161016218193 8735289077271870762163645)
                    ·
                      refine ⟨3275733403976951535811367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8735289077271870762163645 3275733403976951535811367)
                      ·
                        rfl

theorem cell23_6379468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_6379468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379468 prefixEnd_6379468 := by exact prefixLift 6379468
  have htrace : WordTrace (prefixWord ++ tailWord_6379468) baseStart_6379468 baseEnd_6379468 := by
    simpa [prefixWord, tailWord_6379468, baseEnd_6379468] using wordTrace_append hprefix tailTrace_6379468
  have hstable : (prefixWord ++ tailWord_6379468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379468).length < 2 ^ (prefixWord ++ tailWord_6379468).sum := by decide
  have hdescent : baseEnd_6379468 < baseStart_6379468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379491 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 3, 3, 2]
def baseStart_6379491 : Nat := 118140960795 + 6379491 * 2 ^ 59
def prefixEnd_6379491 : Nat := 4983230072969 + 3 ^ 40 * 6379491 * 2
def baseEnd_6379491 : Nat := 3275745214032004945823761

theorem tailTrace_6379491 : CollatzResearch.WordTrace tailWord_6379491 prefixEnd_6379491 3275745214032004945823761 := by
  unfold tailWord_6379491
  simp only [CollatzResearch.WordTrace]
  refine ⟨232679152131201112165970327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155119434754134074777313551 232679152131201112165970327)
  ·
    refine ⟨349018728196801668248955491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232679152131201112165970327 349018728196801668248955491)
    ·
      refine ⟨523528092295202502373433237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349018728196801668248955491 523528092295202502373433237)
      ·
        refine ⟨24540379326337617298754683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 523528092295202502373433237 24540379326337617298754683)
        ·
          refine ⟨36810568989506425948132025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24540379326337617298754683 36810568989506425948132025)
          ·
            refine ⟨27607926742129819461099019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36810568989506425948132025 27607926742129819461099019)
            ·
              refine ⟨41411890113194729191648529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27607926742129819461099019 41411890113194729191648529)
              ·
                refine ⟨31058917584896046893736397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41411890113194729191648529 31058917584896046893736397)
                ·
                  refine ⟨11647094094336017585151149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31058917584896046893736397 11647094094336017585151149)
                  ·
                    refine ⟨4367660285376006594431681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11647094094336017585151149 4367660285376006594431681)
                    ·
                      refine ⟨3275745214032004945823761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4367660285376006594431681 3275745214032004945823761)
                      ·
                        rfl

theorem cell23_6379491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_6379491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379491 prefixEnd_6379491 := by exact prefixLift 6379491
  have htrace : WordTrace (prefixWord ++ tailWord_6379491) baseStart_6379491 baseEnd_6379491 := by
    simpa [prefixWord, tailWord_6379491, baseEnd_6379491] using wordTrace_append hprefix tailTrace_6379491
  have hstable : (prefixWord ++ tailWord_6379491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379491).length < 2 ^ (prefixWord ++ tailWord_6379491).sum := by decide
  have hdescent : baseEnd_6379491 < baseStart_6379491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379507 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 5]
def baseStart_6379507 : Nat := 118140960795 + 6379507 * 2 ^ 59
def prefixEnd_6379507 : Nat := 4983230072969 + 3 ^ 40 * 6379507 * 2
def baseEnd_6379507 : Nat := 3275753429722476883223687

theorem tailTrace_6379507 : CollatzResearch.WordTrace tailWord_6379507 prefixEnd_6379507 3275753429722476883223687 := by
  unfold tailWord_6379507
  simp only [CollatzResearch.WordTrace]
  refine ⟨232679735699143146898552775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155119823799428764599035183 232679735699143146898552775)
  ·
    refine ⟨349019603548714720347829163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232679735699143146898552775 349019603548714720347829163)
    ·
      refine ⟨523529405323072080521743745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349019603548714720347829163 523529405323072080521743745)
      ·
        refine ⟨392647053992304060391307809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523529405323072080521743745 392647053992304060391307809)
        ·
          refine ⟨294485290494228045293480857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392647053992304060391307809 294485290494228045293480857)
          ·
            refine ⟨220863967870671033970110643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294485290494228045293480857 220863967870671033970110643)
            ·
              refine ⟨331295951806006550955165965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220863967870671033970110643 331295951806006550955165965)
              ·
                refine ⟨124235981927252456608187237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331295951806006550955165965 124235981927252456608187237)
                ·
                  refine ⟨23294246611359835614035107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124235981927252456608187237 23294246611359835614035107)
                  ·
                    refine ⟨34941369917039753421052661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23294246611359835614035107 34941369917039753421052661)
                    ·
                      refine ⟨3275753429722476883223687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34941369917039753421052661 3275753429722476883223687)
                      ·
                        rfl

theorem cell23_6379507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 5].length) (baseStart_6379507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379507 prefixEnd_6379507 := by exact prefixLift 6379507
  have htrace : WordTrace (prefixWord ++ tailWord_6379507) baseStart_6379507 baseEnd_6379507 := by
    simpa [prefixWord, tailWord_6379507, baseEnd_6379507] using wordTrace_append hprefix tailTrace_6379507
  have hstable : (prefixWord ++ tailWord_6379507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379507).length < 2 ^ (prefixWord ++ tailWord_6379507).sum := by decide
  have hdescent : baseEnd_6379507 < baseStart_6379507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379521 : List Nat := [1, 2, 4, 1, 2, 1, 1, 4, 1, 4, 2]
def baseStart_6379521 : Nat := 118140960795 + 6379521 * 2 ^ 59
def prefixEnd_6379521 : Nat := 4983230072969 + 3 ^ 40 * 6379521 * 2
def baseEnd_6379521 : Nat := 3275760618451639828448623

theorem tailTrace_6379521 : CollatzResearch.WordTrace tailWord_6379521 prefixEnd_6379521 3275760618451639828448623 := by
  unfold tailWord_6379521
  simp only [CollatzResearch.WordTrace]
  refine ⟨232680246321092427289562417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155120164214061618193041611 232680246321092427289562417)
  ·
    refine ⟨174510184740819320467171813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232680246321092427289562417 174510184740819320467171813)
    ·
      refine ⟨32720659638903622587594715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174510184740819320467171813 32720659638903622587594715)
      ·
        refine ⟨49080989458355433881392073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32720659638903622587594715 49080989458355433881392073)
        ·
          refine ⟨36810742093766575411044055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49080989458355433881392073 36810742093766575411044055)
          ·
            refine ⟨55216113140649863116566083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36810742093766575411044055 55216113140649863116566083)
            ·
              refine ⟨82824169710974794674849125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55216113140649863116566083 82824169710974794674849125)
              ·
                refine ⟨15529531820807774001534211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82824169710974794674849125 15529531820807774001534211)
                ·
                  refine ⟨23294297731211661002301317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15529531820807774001534211 23294297731211661002301317)
                  ·
                    refine ⟨4367680824602186437931497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23294297731211661002301317 4367680824602186437931497)
                    ·
                      refine ⟨3275760618451639828448623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4367680824602186437931497 3275760618451639828448623)
                      ·
                        rfl

theorem cell23_6379521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_6379521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379521 prefixEnd_6379521 := by exact prefixLift 6379521
  have htrace : WordTrace (prefixWord ++ tailWord_6379521) baseStart_6379521 baseEnd_6379521 := by
    simpa [prefixWord, tailWord_6379521, baseEnd_6379521] using wordTrace_append hprefix tailTrace_6379521
  have hstable : (prefixWord ++ tailWord_6379521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379521).length < 2 ^ (prefixWord ++ tailWord_6379521).sum := by decide
  have hdescent : baseEnd_6379521 < baseStart_6379521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379525 : List Nat := [1, 3, 1, 1, 2, 6, 2, 1, 1, 3, 2]
def baseStart_6379525 : Nat := 118140960795 + 6379525 * 2 ^ 59
def prefixEnd_6379525 : Nat := 4983230072969 + 3 ^ 40 * 6379525 * 2
def baseEnd_6379525 : Nat := 3275762672374257812798605

theorem tailTrace_6379525 : CollatzResearch.WordTrace tailWord_6379525 prefixEnd_6379525 3275762672374257812798605 := by
  unfold tailWord_6379525
  simp only [CollatzResearch.WordTrace]
  refine ⟨232680392213077935972708029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155120261475385290648472019 232680392213077935972708029)
  ·
    refine ⟨87255147079904225989765511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232680392213077935972708029 87255147079904225989765511)
    ·
      refine ⟨130882720619856338984648267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87255147079904225989765511 130882720619856338984648267)
      ·
        refine ⟨196324080929784508476972401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130882720619856338984648267 196324080929784508476972401)
        ·
          refine ⟨147243060697338381357729301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196324080929784508476972401 147243060697338381357729301)
          ·
            refine ⟨6902018470187736626143561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 147243060697338381357729301 6902018470187736626143561)
            ·
              refine ⟨5176513852640802469607671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6902018470187736626143561 5176513852640802469607671)
              ·
                refine ⟨7764770778961203704411507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5176513852640802469607671 7764770778961203704411507)
                ·
                  refine ⟨11647156168441805556617261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7764770778961203704411507 11647156168441805556617261)
                  ·
                    refine ⟨4367683563165677083731473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11647156168441805556617261 4367683563165677083731473)
                    ·
                      refine ⟨3275762672374257812798605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4367683563165677083731473 3275762672374257812798605)
                      ·
                        rfl

theorem cell23_6379525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 1, 3, 2].length) (baseStart_6379525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379525 prefixEnd_6379525 := by exact prefixLift 6379525
  have htrace : WordTrace (prefixWord ++ tailWord_6379525) baseStart_6379525 baseEnd_6379525 := by
    simpa [prefixWord, tailWord_6379525, baseEnd_6379525] using wordTrace_append hprefix tailTrace_6379525
  have hstable : (prefixWord ++ tailWord_6379525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379525).length < 2 ^ (prefixWord ++ tailWord_6379525).sum := by decide
  have hdescent : baseEnd_6379525 < baseStart_6379525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379526 : List Nat := [6, 2, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_6379526 : Nat := 118140960795 + 6379526 * 2 ^ 59
def prefixEnd_6379526 : Nat := 4983230072969 + 3 ^ 40 * 6379526 * 2
def baseEnd_6379526 : Nat := 1091921061951637436295367

theorem tailTrace_6379526 : CollatzResearch.WordTrace tailWord_6379526 prefixEnd_6379526 1091921061951637436295367 := by
  unfold tailWord_6379526
  simp only [CollatzResearch.WordTrace]
  refine ⟨7271263396439822285734201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 155120285790716208762329621 7271263396439822285734201)
  ·
    refine ⟨5453447547329866714300651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7271263396439822285734201 5453447547329866714300651)
    ·
      refine ⟨8180171320994800071450977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5453447547329866714300651 8180171320994800071450977)
      ·
        refine ⟨6135128490746100053588233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8180171320994800071450977 6135128490746100053588233)
        ·
          refine ⟨4601346368059575040191175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6135128490746100053588233 4601346368059575040191175)
          ·
            refine ⟨6902019552089362560286763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4601346368059575040191175 6902019552089362560286763)
            ·
              refine ⟨10353029328134043840430145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6902019552089362560286763 10353029328134043840430145)
              ·
                refine ⟨7764771996100532880322609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10353029328134043840430145 7764771996100532880322609)
                ·
                  refine ⟨5823578997075399660241957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7764771996100532880322609 5823578997075399660241957)
                  ·
                    refine ⟨1091921061951637436295367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5823578997075399660241957 1091921061951637436295367)
                    ·
                      rfl

theorem cell23_6379526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_6379526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379526 prefixEnd_6379526 := by exact prefixLift 6379526
  have htrace : WordTrace (prefixWord ++ tailWord_6379526) baseStart_6379526 baseEnd_6379526 := by
    simpa [prefixWord, tailWord_6379526, baseEnd_6379526] using wordTrace_append hprefix tailTrace_6379526
  have hstable : (prefixWord ++ tailWord_6379526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379526).length < 2 ^ (prefixWord ++ tailWord_6379526).sum := by decide
  have hdescent : baseEnd_6379526 < baseStart_6379526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379534 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_6379534 : Nat := 118140960795 + 6379534 * 2 ^ 59
def prefixEnd_6379534 : Nat := 4983230072969 + 3 ^ 40 * 6379534 * 2
def baseEnd_6379534 : Nat := 3275767293700148277586063

theorem tailTrace_6379534 : CollatzResearch.WordTrace tailWord_6379534 prefixEnd_6379534 3275767293700148277586063 := by
  unfold tailWord_6379534
  simp only [CollatzResearch.WordTrace]
  refine ⟨29085090058755666313723207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155120480313363553673190437 29085090058755666313723207)
  ·
    refine ⟨43627635088133499470584811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29085090058755666313723207 43627635088133499470584811)
    ·
      refine ⟨65441452632200249205877217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43627635088133499470584811 65441452632200249205877217)
      ·
        refine ⟨49081089474150186904407913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65441452632200249205877217 49081089474150186904407913)
        ·
          refine ⟨36810817105612640178305935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49081089474150186904407913 36810817105612640178305935)
          ·
            refine ⟨55216225658418960267458903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36810817105612640178305935 55216225658418960267458903)
            ·
              refine ⟨82824338487628440401188355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55216225658418960267458903 82824338487628440401188355)
              ·
                refine ⟨124236507731442660601782533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82824338487628440401188355 124236507731442660601782533)
                ·
                  refine ⟨23294345199645498862834225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124236507731442660601782533 23294345199645498862834225)
                  ·
                    refine ⟨17470758899734124147125669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23294345199645498862834225 17470758899734124147125669)
                    ·
                      refine ⟨3275767293700148277586063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17470758899734124147125669 3275767293700148277586063)
                      ·
                        rfl

theorem cell23_6379534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_6379534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379534 prefixEnd_6379534 := by exact prefixLift 6379534
  have htrace : WordTrace (prefixWord ++ tailWord_6379534) baseStart_6379534 baseEnd_6379534 := by
    simpa [prefixWord, tailWord_6379534, baseEnd_6379534] using wordTrace_append hprefix tailTrace_6379534
  have hstable : (prefixWord ++ tailWord_6379534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379534).length < 2 ^ (prefixWord ++ tailWord_6379534).sum := by decide
  have hdescent : baseEnd_6379534 < baseStart_6379534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379544 : List Nat := [2, 1, 2, 3, 2, 1, 4, 1, 7]
def baseStart_6379544 : Nat := 118140960795 + 6379544 * 2 ^ 59
def prefixEnd_6379544 : Nat := 4983230072969 + 3 ^ 40 * 6379544 * 2
def baseEnd_6379544 : Nat := 363974714278521470940113

theorem tailTrace_6379544 : CollatzResearch.WordTrace tailWord_6379544 prefixEnd_6379544 363974714278521470940113 := by
  unfold tailWord_6379544
  simp only [CollatzResearch.WordTrace]
  refine ⟨116340542600004551108824843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155120723466672734811766457 116340542600004551108824843)
  ·
    refine ⟨174510813900006826663237265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116340542600004551108824843 174510813900006826663237265)
    ·
      refine ⟨130883110425005119997427949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174510813900006826663237265 130883110425005119997427949)
      ·
        refine ⟨49081166409376919999035481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130883110425005119997427949 49081166409376919999035481)
        ·
          refine ⟨36810874807032689999276611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49081166409376919999035481 36810874807032689999276611)
          ·
            refine ⟨55216312210549034998914917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36810874807032689999276611 55216312210549034998914917)
            ·
              refine ⟨10353058539477944062296547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55216312210549034998914917 10353058539477944062296547)
              ·
                refine ⟨15529587809216916093444821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10353058539477944062296547 15529587809216916093444821)
                ·
                  refine ⟨363974714278521470940113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15529587809216916093444821 363974714278521470940113)
                  ·
                    rfl

theorem cell23_6379544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 7].length) (baseStart_6379544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379544 prefixEnd_6379544 := by exact prefixLift 6379544
  have htrace : WordTrace (prefixWord ++ tailWord_6379544) baseStart_6379544 baseEnd_6379544 := by
    simpa [prefixWord, tailWord_6379544, baseEnd_6379544] using wordTrace_append hprefix tailTrace_6379544
  have hstable : (prefixWord ++ tailWord_6379544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379544).length < 2 ^ (prefixWord ++ tailWord_6379544).sum := by decide
  have hdescent : baseEnd_6379544 < baseStart_6379544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379555 : List Nat := [1, 1, 1, 4, 3, 1, 5, 1, 2, 2, 2]
def baseStart_6379555 : Nat := 118140960795 + 6379555 * 2 ^ 59
def prefixEnd_6379555 : Nat := 4983230072969 + 3 ^ 40 * 6379555 * 2
def baseEnd_6379555 : Nat := 3275778076793892695423467

theorem tailTrace_6379555 : CollatzResearch.WordTrace tailWord_6379555 prefixEnd_6379555 3275778076793892695423467 := by
  unfold tailWord_6379555
  simp only [CollatzResearch.WordTrace]
  refine ⟨232681486402969251096300119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155120990935312834064200079 232681486402969251096300119)
  ·
    refine ⟨349022229604453876644450179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232681486402969251096300119 349022229604453876644450179)
    ·
      refine ⟨523533344406680814966675269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349022229604453876644450179 523533344406680814966675269)
      ·
        refine ⟨98162502076252652806251613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 523533344406680814966675269 98162502076252652806251613)
        ·
          refine ⟨36810938278594744802344355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98162502076252652806251613 36810938278594744802344355)
          ·
            refine ⟨55216407417892117203516533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36810938278594744802344355 55216407417892117203516533)
            ·
              refine ⟨5176538195427385987829675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55216407417892117203516533 5176538195427385987829675)
              ·
                refine ⟨7764807293141078981744513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5176538195427385987829675 7764807293141078981744513)
                ·
                  refine ⟨5823605469855809236308385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7764807293141078981744513 5823605469855809236308385)
                  ·
                    refine ⟨4367704102391856927231289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5823605469855809236308385 4367704102391856927231289)
                    ·
                      refine ⟨3275778076793892695423467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4367704102391856927231289 3275778076793892695423467)
                      ·
                        rfl

theorem cell23_6379555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_6379555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379555 prefixEnd_6379555 := by exact prefixLift 6379555
  have htrace : WordTrace (prefixWord ++ tailWord_6379555) baseStart_6379555 baseEnd_6379555 := by
    simpa [prefixWord, tailWord_6379555, baseEnd_6379555] using wordTrace_append hprefix tailTrace_6379555
  have hstable : (prefixWord ++ tailWord_6379555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379555).length < 2 ^ (prefixWord ++ tailWord_6379555).sum := by decide
  have hdescent : baseEnd_6379555 < baseStart_6379555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379567 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 7]
def baseStart_6379567 : Nat := 118140960795 + 6379567 * 2 ^ 59
def prefixEnd_6379567 : Nat := 4983230072969 + 3 ^ 40 * 6379567 * 2
def baseEnd_6379567 : Nat := 3275784238561746648473411

theorem tailTrace_6379567 : CollatzResearch.WordTrace tailWord_6379567 prefixEnd_6379567 3275784238561746648473411 := by
  unfold tailWord_6379567
  simp only [CollatzResearch.WordTrace]
  refine ⟨232681924078925777145736955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155121282719283851430491303 232681924078925777145736955)
  ·
    refine ⟨349022886118388665718605433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232681924078925777145736955 349022886118388665718605433)
    ·
      refine ⟨261767164588791499288954075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349022886118388665718605433 261767164588791499288954075)
      ·
        refine ⟨392650746883187248933431113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261767164588791499288954075 392650746883187248933431113)
        ·
          refine ⟨294488060162390436700073335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392650746883187248933431113 294488060162390436700073335)
          ·
            refine ⟨441732090243585655050110003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294488060162390436700073335 441732090243585655050110003)
            ·
              refine ⟨662598135365378482575165005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441732090243585655050110003 662598135365378482575165005)
              ·
                refine ⟨248474300762016930965686877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 662598135365378482575165005 248474300762016930965686877)
                ·
                  refine ⟨93177862785756349112132579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 248474300762016930965686877 93177862785756349112132579)
                  ·
                    refine ⟨139766794178634523668198869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93177862785756349112132579 139766794178634523668198869)
                    ·
                      refine ⟨3275784238561746648473411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139766794178634523668198869 3275784238561746648473411)
                      ·
                        rfl

theorem cell23_6379567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_6379567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379567 prefixEnd_6379567 := by exact prefixLift 6379567
  have htrace : WordTrace (prefixWord ++ tailWord_6379567) baseStart_6379567 baseEnd_6379567 := by
    simpa [prefixWord, tailWord_6379567, baseEnd_6379567] using wordTrace_append hprefix tailTrace_6379567
  have hstable : (prefixWord ++ tailWord_6379567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379567).length < 2 ^ (prefixWord ++ tailWord_6379567).sum := by decide
  have hdescent : baseEnd_6379567 < baseStart_6379567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379606 : List Nat := [5, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_6379606 : Nat := 118140960795 + 6379606 * 2 ^ 59
def prefixEnd_6379606 : Nat := 4983230072969 + 3 ^ 40 * 6379606 * 2
def baseEnd_6379606 : Nat := 3275804264307271995885733

theorem tailTrace_6379606 : CollatzResearch.WordTrace tailWord_6379606 prefixEnd_6379606 3275804264307271995885733 := by
  unfold tailWord_6379606
  simp only [CollatzResearch.WordTrace]
  refine ⟨14542709157861530425400417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155122231017189657870937781 14542709157861530425400417)
  ·
    refine ⟨10907031868396147819050313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14542709157861530425400417 10907031868396147819050313)
    ·
      refine ⟨8180273901297110864287735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10907031868396147819050313 8180273901297110864287735)
      ·
        refine ⟨12270410851945666296431603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8180273901297110864287735 12270410851945666296431603)
        ·
          refine ⟨18405616277918499444647405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12270410851945666296431603 18405616277918499444647405)
          ·
            refine ⟨6902106104219437291742777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18405616277918499444647405 6902106104219437291742777)
            ·
              refine ⟨5176579578164577968807083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6902106104219437291742777 5176579578164577968807083)
              ·
                refine ⟨7764869367246866953210625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5176579578164577968807083 7764869367246866953210625)
                ·
                  refine ⟨5823652025435150214907969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7764869367246866953210625 5823652025435150214907969)
                  ·
                    refine ⟨4367739019076362661180977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5823652025435150214907969 4367739019076362661180977)
                    ·
                      refine ⟨3275804264307271995885733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4367739019076362661180977 3275804264307271995885733)
                      ·
                        rfl

theorem cell23_6379606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_6379606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379606 prefixEnd_6379606 := by exact prefixLift 6379606
  have htrace : WordTrace (prefixWord ++ tailWord_6379606) baseStart_6379606 baseEnd_6379606 := by
    simpa [prefixWord, tailWord_6379606, baseEnd_6379606] using wordTrace_append hprefix tailTrace_6379606
  have hstable : (prefixWord ++ tailWord_6379606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379606).length < 2 ^ (prefixWord ++ tailWord_6379606).sum := by decide
  have hdescent : baseEnd_6379606 < baseStart_6379606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379631 : List Nat := [1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 3]
def baseStart_6379631 : Nat := 118140960795 + 6379631 * 2 ^ 59
def prefixEnd_6379631 : Nat := 4983230072969 + 3 ^ 40 * 6379631 * 2
def baseEnd_6379631 : Nat := 3275817101323634398073117

theorem tailTrace_6379631 : CollatzResearch.WordTrace tailWord_6379631 prefixEnd_6379631 3275817101323634398073117 := by
  unfold tailWord_6379631
  simp only [CollatzResearch.WordTrace]
  refine ⟨232684258350693916076066747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155122838900462610717377831 232684258350693916076066747)
  ·
    refine ⟨349026387526040874114100121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232684258350693916076066747 349026387526040874114100121)
    ·
      refine ⟨261769790644530655585575091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349026387526040874114100121 261769790644530655585575091)
      ·
        refine ⟨392654685966795983378362637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261769790644530655585575091 392654685966795983378362637)
        ·
          refine ⟨147245507237548493766885989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392654685966795983378362637 147245507237548493766885989)
          ·
            refine ⟨27608532607040342581291123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147245507237548493766885989 27608532607040342581291123)
            ·
              refine ⟨41412798910560513871936685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27608532607040342581291123 41412798910560513871936685)
              ·
                refine ⟨15529799591460192701976257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41412798910560513871936685 15529799591460192701976257)
                ·
                  refine ⟨11647349693595144526482193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15529799591460192701976257 11647349693595144526482193)
                  ·
                    refine ⟨8735512270196358394861645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11647349693595144526482193 8735512270196358394861645)
                    ·
                      refine ⟨3275817101323634398073117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8735512270196358394861645 3275817101323634398073117)
                      ·
                        rfl

theorem cell23_6379631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 3].length) (baseStart_6379631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379631 prefixEnd_6379631 := by exact prefixLift 6379631
  have htrace : WordTrace (prefixWord ++ tailWord_6379631) baseStart_6379631 baseEnd_6379631 := by
    simpa [prefixWord, tailWord_6379631, baseEnd_6379631] using wordTrace_append hprefix tailTrace_6379631
  have hstable : (prefixWord ++ tailWord_6379631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379631).length < 2 ^ (prefixWord ++ tailWord_6379631).sum := by decide
  have hdescent : baseEnd_6379631 < baseStart_6379631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379651 : List Nat := [1, 1, 1, 3, 3, 4, 2, 2, 6]
def baseStart_6379651 : Nat := 118140960795 + 6379651 * 2 ^ 59
def prefixEnd_6379651 : Nat := 4983230072969 + 3 ^ 40 * 6379651 * 2
def baseEnd_6379651 : Nat := 363980818992969368869225

theorem tailTrace_6379651 : CollatzResearch.WordTrace tailWord_6379651 prefixEnd_6379651 363980818992969368869225 := by
  unfold tailWord_6379651
  simp only [CollatzResearch.WordTrace]
  refine ⟨232684987810621459491794807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155123325207080972994529871 232684987810621459491794807)
  ·
    refine ⟨349027481715932189237692211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232684987810621459491794807 349027481715932189237692211)
    ·
      refine ⟨523541222573898283856538317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349027481715932189237692211 523541222573898283856538317)
      ·
        refine ⟨196327958465211856446201869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 523541222573898283856538317 196327958465211856446201869)
        ·
          refine ⟨73622984424454446167325701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196327958465211856446201869 73622984424454446167325701)
          ·
            refine ⟨13804309579585208656373569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73622984424454446167325701 13804309579585208656373569)
            ·
              refine ⟨10353232184688906492280177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13804309579585208656373569 10353232184688906492280177)
              ·
                refine ⟨7764924138516679869210133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10353232184688906492280177 7764924138516679869210133)
                ·
                  refine ⟨363980818992969368869225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7764924138516679869210133 363980818992969368869225)
                  ·
                    rfl

theorem cell23_6379651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 6].length) (baseStart_6379651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379651 prefixEnd_6379651 := by exact prefixLift 6379651
  have htrace : WordTrace (prefixWord ++ tailWord_6379651) baseStart_6379651 baseEnd_6379651 := by
    simpa [prefixWord, tailWord_6379651, baseEnd_6379651] using wordTrace_append hprefix tailTrace_6379651
  have hstable : (prefixWord ++ tailWord_6379651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379651).length < 2 ^ (prefixWord ++ tailWord_6379651).sum := by decide
  have hdescent : baseEnd_6379651 < baseStart_6379651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379655 : List Nat := [1, 1, 4, 2, 1, 1, 6, 2, 1, 4]
def baseStart_6379655 : Nat := 118140960795 + 6379655 * 2 ^ 59
def prefixEnd_6379655 : Nat := 4983230072969 + 3 ^ 40 * 6379655 * 2
def baseEnd_6379655 : Nat := 1091943141619780768057669

theorem tailTrace_6379655 : CollatzResearch.WordTrace tailWord_6379655 prefixEnd_6379655 1091943141619780768057669 := by
  unfold tailWord_6379655
  simp only [CollatzResearch.WordTrace]
  refine ⟨232685133702606968174940419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155123422468404645449960279 232685133702606968174940419)
  ·
    refine ⟨349027700553910452262410629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232685133702606968174940419 349027700553910452262410629)
    ·
      refine ⟨65442693853858209799201993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 349027700553910452262410629 65442693853858209799201993)
      ·
        refine ⟨49082020390393657349401495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65442693853858209799201993 49082020390393657349401495)
        ·
          refine ⟨73623030585590486024102243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49082020390393657349401495 73623030585590486024102243)
          ·
            refine ⟨110434545878385729036153365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73623030585590486024102243 110434545878385729036153365)
            ·
              refine ⟨5176619338049331048569689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110434545878385729036153365 5176619338049331048569689)
              ·
                refine ⟨3882464503536998286427267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5176619338049331048569689 3882464503536998286427267)
                ·
                  refine ⟨5823696755305497429640901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3882464503536998286427267 5823696755305497429640901)
                  ·
                    refine ⟨1091943141619780768057669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5823696755305497429640901 1091943141619780768057669)
                    ·
                      rfl

theorem cell23_6379655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_6379655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379655 prefixEnd_6379655 := by exact prefixLift 6379655
  have htrace : WordTrace (prefixWord ++ tailWord_6379655) baseStart_6379655 baseEnd_6379655 := by
    simpa [prefixWord, tailWord_6379655, baseEnd_6379655] using wordTrace_append hprefix tailTrace_6379655
  have hstable : (prefixWord ++ tailWord_6379655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379655).length < 2 ^ (prefixWord ++ tailWord_6379655).sum := by decide
  have hdescent : baseEnd_6379655 < baseStart_6379655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379664 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 5, 5]
def baseStart_6379664 : Nat := 118140960795 + 6379664 * 2 ^ 59
def prefixEnd_6379664 : Nat := 4983230072969 + 3 ^ 40 * 6379664 * 2
def baseEnd_6379664 : Nat := 1091944682061744256320155

theorem tailTrace_6379664 : CollatzResearch.WordTrace tailWord_6379664 prefixEnd_6379664 1091944682061744256320155 := by
  unfold tailWord_6379664
  simp only [CollatzResearch.WordTrace]
  refine ⟨116342730979787181356009023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155123641306382908474678697 116342730979787181356009023)
  ·
    refine ⟨174514096469680772034013535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116342730979787181356009023 174514096469680772034013535)
    ·
      refine ⟨261771144704521158051020303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174514096469680772034013535 261771144704521158051020303)
      ·
        refine ⟨392656717056781737076530455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261771144704521158051020303 392656717056781737076530455)
        ·
          refine ⟨588985075585172605614795683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392656717056781737076530455 588985075585172605614795683)
          ·
            refine ⟨883477613377758908422193525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588985075585172605614795683 883477613377758908422193525)
            ·
              refine ⟨82826026254164897664580643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 883477613377758908422193525 82826026254164897664580643)
              ·
                refine ⟨124239039381247346496870965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82826026254164897664580643 124239039381247346496870965)
                ·
                  refine ⟨11647409941991938734081653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124239039381247346496870965 11647409941991938734081653)
                  ·
                    refine ⟨1091944682061744256320155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11647409941991938734081653 1091944682061744256320155)
                    ·
                      rfl

theorem cell23_6379664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 5, 5].length) (baseStart_6379664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379664 prefixEnd_6379664 := by exact prefixLift 6379664
  have htrace : WordTrace (prefixWord ++ tailWord_6379664) baseStart_6379664 baseEnd_6379664 := by
    simpa [prefixWord, tailWord_6379664, baseEnd_6379664] using wordTrace_append hprefix tailTrace_6379664
  have hstable : (prefixWord ++ tailWord_6379664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379664).length < 2 ^ (prefixWord ++ tailWord_6379664).sum := by decide
  have hdescent : baseEnd_6379664 < baseStart_6379664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379681 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 3, 5]
def baseStart_6379681 : Nat := 118140960795 + 6379681 * 2 ^ 59
def prefixEnd_6379681 : Nat := 4983230072969 + 3 ^ 40 * 6379681 * 2
def baseEnd_6379681 : Nat := 1091947591785453067482629

theorem tailTrace_6379681 : CollatzResearch.WordTrace tailWord_6379681 prefixEnd_6379681 1091947591785453067482629 := by
  unfold tailWord_6379681
  simp only [CollatzResearch.WordTrace]
  refine ⟨232686082000512774615386897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155124054667008516410257931 232686082000512774615386897)
  ·
    refine ⟨174514561500384580961540173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232686082000512774615386897 174514561500384580961540173)
    ·
      refine ⟨65442960562644217860577565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174514561500384580961540173 65442960562644217860577565)
      ·
        refine ⟨24541110210991581697716587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65442960562644217860577565 24541110210991581697716587)
        ·
          refine ⟨36811665316487372546574881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24541110210991581697716587 36811665316487372546574881)
          ·
            refine ⟨27608748987365529409931161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36811665316487372546574881 27608748987365529409931161)
            ·
              refine ⟨20706561740524147057448371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27608748987365529409931161 20706561740524147057448371)
              ·
                refine ⟨31059842610786220586172557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20706561740524147057448371 31059842610786220586172557)
                ·
                  refine ⟨11647440979044832719814709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31059842610786220586172557 11647440979044832719814709)
                  ·
                    refine ⟨1091947591785453067482629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11647440979044832719814709 1091947591785453067482629)
                    ·
                      rfl

theorem cell23_6379681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_6379681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379681 prefixEnd_6379681 := by exact prefixLift 6379681
  have htrace : WordTrace (prefixWord ++ tailWord_6379681) baseStart_6379681 baseEnd_6379681 := by
    simpa [prefixWord, tailWord_6379681, baseEnd_6379681] using wordTrace_append hprefix tailTrace_6379681
  have hstable : (prefixWord ++ tailWord_6379681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379681).length < 2 ^ (prefixWord ++ tailWord_6379681).sum := by decide
  have hdescent : baseEnd_6379681 < baseStart_6379681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379721 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 3, 2, 3]
def baseStart_6379721 : Nat := 118140960795 + 6379721 * 2 ^ 59
def prefixEnd_6379721 : Nat := 4983230072969 + 3 ^ 40 * 6379721 * 2
def baseEnd_6379721 : Nat := 3275863314582539045947703

theorem tailTrace_6379721 : CollatzResearch.WordTrace tailWord_6379721 prefixEnd_6379721 3275863314582539045947703 := by
  unfold tailWord_6379721
  simp only [CollatzResearch.WordTrace]
  refine ⟨232687540920367861446843017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155125027280245240964562011 232687540920367861446843017)
  ·
    refine ⟨174515655690275896085132263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232687540920367861446843017 174515655690275896085132263)
    ·
      refine ⟨261773483535413844127698395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174515655690275896085132263 261773483535413844127698395)
      ·
        refine ⟨392660225303120766191547593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261773483535413844127698395 392660225303120766191547593)
        ·
          refine ⟨294495168977340574643660695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392660225303120766191547593 294495168977340574643660695)
          ·
            refine ⟨441742753466010861965491043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294495168977340574643660695 441742753466010861965491043)
            ·
              refine ⟨662614130199016292948236565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441742753466010861965491043 662614130199016292948236565)
              ·
                refine ⟨31060037353078888731948589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 662614130199016292948236565 31060037353078888731948589)
                ·
                  refine ⟨11647514007404583274480721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31060037353078888731948589 11647514007404583274480721)
                  ·
                    refine ⟨8735635505553437455860541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11647514007404583274480721 8735635505553437455860541)
                    ·
                      refine ⟨3275863314582539045947703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8735635505553437455860541 3275863314582539045947703)
                      ·
                        rfl

theorem cell23_6379721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 2, 3].length) (baseStart_6379721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379721 prefixEnd_6379721 := by exact prefixLift 6379721
  have htrace : WordTrace (prefixWord ++ tailWord_6379721) baseStart_6379721 baseEnd_6379721 := by
    simpa [prefixWord, tailWord_6379721, baseEnd_6379721] using wordTrace_append hprefix tailTrace_6379721
  have hstable : (prefixWord ++ tailWord_6379721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379721).length < 2 ^ (prefixWord ++ tailWord_6379721).sum := by decide
  have hdescent : baseEnd_6379721 < baseStart_6379721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379738 : List Nat := [3, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3]
def baseStart_6379738 : Nat := 118140960795 + 6379738 * 2 ^ 59
def prefixEnd_6379738 : Nat := 4983230072969 + 3 ^ 40 * 6379738 * 2
def baseEnd_6379738 : Nat := 3275872043753665479435125

theorem tailTrace_6379738 : CollatzResearch.WordTrace tailWord_6379738 prefixEnd_6379738 3275872043753665479435125 := by
  unfold tailWord_6379738
  simp only [CollatzResearch.WordTrace]
  refine ⟨58172040240326568337552967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155125440640870848900141245 58172040240326568337552967)
  ·
    refine ⟨87258060360489852506329451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58172040240326568337552967 87258060360489852506329451)
    ·
      refine ⟨130887090540734778759494177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87258060360489852506329451 130887090540734778759494177)
      ·
        refine ⟨98165317905551084069620633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130887090540734778759494177 98165317905551084069620633)
        ·
          refine ⟨73623988429163313052215475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98165317905551084069620633 73623988429163313052215475)
          ·
            refine ⟨110435982643744969578323213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73623988429163313052215475 110435982643744969578323213)
            ·
              refine ⟨41413493491404363591871205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110435982643744969578323213 41413493491404363591871205)
              ·
                refine ⟨7765030029638318173475851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41413493491404363591871205 7765030029638318173475851)
                ·
                  refine ⟨11647545044457477260213777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7765030029638318173475851 11647545044457477260213777)
                  ·
                    refine ⟨8735658783343107945160333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11647545044457477260213777 8735658783343107945160333)
                    ·
                      refine ⟨3275872043753665479435125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8735658783343107945160333 3275872043753665479435125)
                      ·
                        rfl

theorem cell23_6379738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_6379738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379738 prefixEnd_6379738 := by exact prefixLift 6379738
  have htrace : WordTrace (prefixWord ++ tailWord_6379738) baseStart_6379738 baseEnd_6379738 := by
    simpa [prefixWord, tailWord_6379738, baseEnd_6379738] using wordTrace_append hprefix tailTrace_6379738
  have hstable : (prefixWord ++ tailWord_6379738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379738).length < 2 ^ (prefixWord ++ tailWord_6379738).sum := by decide
  have hdescent : baseEnd_6379738 < baseStart_6379738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379785 : List Nat := [1, 2, 1, 1, 3, 5, 1, 3, 2, 1, 3]
def baseStart_6379785 : Nat := 118140960795 + 6379785 * 2 ^ 59
def prefixEnd_6379785 : Nat := 4983230072969 + 3 ^ 40 * 6379785 * 2
def baseEnd_6379785 : Nat := 3275896177344426795547409

theorem tailTrace_6379785 : CollatzResearch.WordTrace tailWord_6379785 prefixEnd_6379785 3275896177344426795547409 := by
  unfold tailWord_6379785
  simp only [CollatzResearch.WordTrace]
  refine ⟨232689875192136000377172809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155126583461424000251448539 232689875192136000377172809)
  ·
    refine ⟨174517406394102000282879607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232689875192136000377172809 174517406394102000282879607)
    ·
      refine ⟨261776109591153000424319411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174517406394102000282879607 261776109591153000424319411)
      ·
        refine ⟨392664164386729500636479117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261776109591153000424319411 392664164386729500636479117)
        ·
          refine ⟨147249061645023562738679669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392664164386729500636479117 147249061645023562738679669)
          ·
            refine ⟨13804599529220959006751219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147249061645023562738679669 13804599529220959006751219)
            ·
              refine ⟨20706899293831438510126829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13804599529220959006751219 20706899293831438510126829)
              ·
                refine ⟨7765087235186789441297561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20706899293831438510126829 7765087235186789441297561)
                ·
                  refine ⟨5823815426390092080973171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7765087235186789441297561 5823815426390092080973171)
                  ·
                    refine ⟨8735723139585138121459757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5823815426390092080973171 8735723139585138121459757)
                    ·
                      refine ⟨3275896177344426795547409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8735723139585138121459757 3275896177344426795547409)
                      ·
                        rfl

theorem cell23_6379785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 1, 3].length) (baseStart_6379785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379785 prefixEnd_6379785 := by exact prefixLift 6379785
  have htrace : WordTrace (prefixWord ++ tailWord_6379785) baseStart_6379785 baseEnd_6379785 := by
    simpa [prefixWord, tailWord_6379785, baseEnd_6379785] using wordTrace_append hprefix tailTrace_6379785
  have hstable : (prefixWord ++ tailWord_6379785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379785).length < 2 ^ (prefixWord ++ tailWord_6379785).sum := by decide
  have hdescent : baseEnd_6379785 < baseStart_6379785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379811 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 5]
def baseStart_6379811 : Nat := 118140960795 + 6379811 * 2 ^ 59
def prefixEnd_6379811 : Nat := 4983230072969 + 3 ^ 40 * 6379811 * 2
def baseEnd_6379811 : Nat := 3275909527841443693822289

theorem tailTrace_6379811 : CollatzResearch.WordTrace tailWord_6379811 prefixEnd_6379811 3275909527841443693822289 := by
  unfold tailWord_6379811
  simp only [CollatzResearch.WordTrace]
  refine ⟨232690823490041806817619287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155127215660027871211746191 232690823490041806817619287)
  ·
    refine ⟨349036235235062710226428931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232690823490041806817619287 349036235235062710226428931)
    ·
      refine ⟨523554352852594065339643397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349036235235062710226428931 523554352852594065339643397)
      ·
        refine ⟨98166441159861387251183137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 523554352852594065339643397 98166441159861387251183137)
        ·
          refine ⟨73624830869896040438387353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98166441159861387251183137 73624830869896040438387353)
          ·
            refine ⟨55218623152422030328790515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73624830869896040438387353 55218623152422030328790515)
            ·
              refine ⟨82827934728633045493185773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55218623152422030328790515 82827934728633045493185773)
              ·
                refine ⟨31060475523237392059944665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82827934728633045493185773 31060475523237392059944665)
                ·
                  refine ⟨23295356642428044044958499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31060475523237392059944665 23295356642428044044958499)
                  ·
                    refine ⟨34943034963642066067437749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23295356642428044044958499 34943034963642066067437749)
                    ·
                      refine ⟨3275909527841443693822289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34943034963642066067437749 3275909527841443693822289)
                      ·
                        rfl

theorem cell23_6379811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_6379811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379811 prefixEnd_6379811 := by exact prefixLift 6379811
  have htrace : WordTrace (prefixWord ++ tailWord_6379811) baseStart_6379811 baseEnd_6379811 := by
    simpa [prefixWord, tailWord_6379811, baseEnd_6379811] using wordTrace_append hprefix tailTrace_6379811
  have hstable : (prefixWord ++ tailWord_6379811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379811).length < 2 ^ (prefixWord ++ tailWord_6379811).sum := by decide
  have hdescent : baseEnd_6379811 < baseStart_6379811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379838 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_6379838 : Nat := 118140960795 + 6379838 * 2 ^ 59
def prefixEnd_6379838 : Nat := 4983230072969 + 3 ^ 40 * 6379838 * 2
def baseEnd_6379838 : Nat := 3275923391819115088184665

theorem tailTrace_6379838 : CollatzResearch.WordTrace tailWord_6379838 prefixEnd_6379838 3275923391819115088184665 := by
  unfold tailWord_6379838
  simp only [CollatzResearch.WordTrace]
  refine ⟨29086476032617998803606521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155127872173962660285901445 29086476032617998803606521)
  ·
    refine ⟨21814857024463499102704891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29086476032617998803606521 21814857024463499102704891)
    ·
      refine ⟨32722285536695248654057337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21814857024463499102704891 32722285536695248654057337)
      ·
        refine ⟨24541714152521436490543003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32722285536695248654057337 24541714152521436490543003)
        ·
          refine ⟨36812571228782154735814505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24541714152521436490543003 36812571228782154735814505)
          ·
            refine ⟨27609428421586616051860879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36812571228782154735814505 27609428421586616051860879)
            ·
              refine ⟨41414142632379924077791319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27609428421586616051860879 41414142632379924077791319)
              ·
                refine ⟨62121213948569886116686979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41414142632379924077791319 62121213948569886116686979)
                ·
                  refine ⟨93181820922854829175030469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62121213948569886116686979 93181820922854829175030469)
                  ·
                    refine ⟨17471591423035280470318213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93181820922854829175030469 17471591423035280470318213)
                    ·
                      refine ⟨3275923391819115088184665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17471591423035280470318213 3275923391819115088184665)
                      ·
                        rfl

theorem cell23_6379838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_6379838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379838 prefixEnd_6379838 := by exact prefixLift 6379838
  have htrace : WordTrace (prefixWord ++ tailWord_6379838) baseStart_6379838 baseEnd_6379838 := by
    simpa [prefixWord, tailWord_6379838, baseEnd_6379838] using wordTrace_append hprefix tailTrace_6379838
  have hstable : (prefixWord ++ tailWord_6379838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379838).length < 2 ^ (prefixWord ++ tailWord_6379838).sum := by decide
  have hdescent : baseEnd_6379838 < baseStart_6379838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379870 : List Nat := [4, 4, 2, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_6379870 : Nat := 118140960795 + 6379870 * 2 ^ 59
def prefixEnd_6379870 : Nat := 4983230072969 + 3 ^ 40 * 6379870 * 2
def baseEnd_6379870 : Nat := 3275939823200058962984519

theorem tailTrace_6379870 : CollatzResearch.WordTrace tailWord_6379870 prefixEnd_6379870 3275939823200058962984519 := by
  unfold tailWord_6379870
  simp only [CollatzResearch.WordTrace]
  refine ⟨29086621924603507486752133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155128650264552039929344709 29086621924603507486752133)
  ·
    refine ⟨5453741610863157653766025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29086621924603507486752133 5453741610863157653766025)
    ·
      refine ⟨4090306208147368240324519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5453741610863157653766025 4090306208147368240324519)
      ·
        refine ⟨6135459312221052360486779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4090306208147368240324519 6135459312221052360486779)
        ·
          refine ⟨9203188968331578540730169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6135459312221052360486779 9203188968331578540730169)
          ·
            refine ⟨6902391726248683905547627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9203188968331578540730169 6902391726248683905547627)
            ·
              refine ⟨10353587589373025858321441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6902391726248683905547627 10353587589373025858321441)
              ·
                refine ⟨7765190692029769393741081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10353587589373025858321441 7765190692029769393741081)
                ·
                  refine ⟨5823893019022327045305811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7765190692029769393741081 5823893019022327045305811)
                  ·
                    refine ⟨8735839528533490567958717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5823893019022327045305811 8735839528533490567958717)
                    ·
                      refine ⟨3275939823200058962984519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8735839528533490567958717 3275939823200058962984519)
                      ·
                        rfl

theorem cell23_6379870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_6379870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379870 prefixEnd_6379870 := by exact prefixLift 6379870
  have htrace : WordTrace (prefixWord ++ tailWord_6379870) baseStart_6379870 baseEnd_6379870 := by
    simpa [prefixWord, tailWord_6379870, baseEnd_6379870] using wordTrace_append hprefix tailTrace_6379870
  have hstable : (prefixWord ++ tailWord_6379870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379870).length < 2 ^ (prefixWord ++ tailWord_6379870).sum := by decide
  have hdescent : baseEnd_6379870 < baseStart_6379870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379871 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 5]
def baseStart_6379871 : Nat := 118140960795 + 6379871 * 2 ^ 59
def prefixEnd_6379871 : Nat := 4983230072969 + 3 ^ 40 * 6379871 * 2
def baseEnd_6379871 : Nat := 3275940336680713459072013

theorem tailTrace_6379871 : CollatzResearch.WordTrace tailWord_6379871 prefixEnd_6379871 3275940336680713459072013 := by
  unfold tailWord_6379871
  simp only [CollatzResearch.WordTrace]
  refine ⟨232693011869824437064803467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155128674579882958043202311 232693011869824437064803467)
  ·
    refine ⟨349039517804736655597205201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232693011869824437064803467 349039517804736655597205201)
    ·
      refine ⟨261779638353552491697903901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349039517804736655597205201 261779638353552491697903901)
      ·
        refine ⟨98167364382582184386713963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261779638353552491697903901 98167364382582184386713963)
        ·
          refine ⟨147251046573873276580070945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98167364382582184386713963 147251046573873276580070945)
          ·
            refine ⟨110438284930404957435053209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147251046573873276580070945 110438284930404957435053209)
            ·
              refine ⟨82828713697803718076289907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110438284930404957435053209 82828713697803718076289907)
              ·
                refine ⟨124243070546705577114434861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82828713697803718076289907 124243070546705577114434861)
                ·
                  refine ⟨46591151455014591417913073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124243070546705577114434861 46591151455014591417913073)
                  ·
                    refine ⟨34943363591260943563434805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46591151455014591417913073 34943363591260943563434805)
                    ·
                      refine ⟨3275940336680713459072013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34943363591260943563434805 3275940336680713459072013)
                      ·
                        rfl

theorem cell23_6379871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_6379871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379871 prefixEnd_6379871 := by exact prefixLift 6379871
  have htrace : WordTrace (prefixWord ++ tailWord_6379871) baseStart_6379871 baseEnd_6379871 := by
    simpa [prefixWord, tailWord_6379871, baseEnd_6379871] using wordTrace_append hprefix tailTrace_6379871
  have hstable : (prefixWord ++ tailWord_6379871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379871).length < 2 ^ (prefixWord ++ tailWord_6379871).sum := by decide
  have hdescent : baseEnd_6379871 < baseStart_6379871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379935 : List Nat := [1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 3]
def baseStart_6379935 : Nat := 118140960795 + 6379935 * 2 ^ 59
def prefixEnd_6379935 : Nat := 4983230072969 + 3 ^ 40 * 6379935 * 2
def baseEnd_6379935 : Nat := 3275973199442601208671719

theorem tailTrace_6379935 : CollatzResearch.WordTrace tailWord_6379935 prefixEnd_6379935 3275973199442601208671719 := by
  unfold tailWord_6379935
  simp only [CollatzResearch.WordTrace]
  refine ⟨232695346141592575995133259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155130230761061717330088839 232695346141592575995133259)
  ·
    refine ⟨349043019212388863992699889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232695346141592575995133259 349043019212388863992699889)
    ·
      refine ⟨261782264409291647994524917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349043019212388863992699889 261782264409291647994524917)
      ·
        refine ⟨24542087288371091999486711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 261782264409291647994524917 24542087288371091999486711)
        ·
          refine ⟨36813130932556637999230067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24542087288371091999486711 36813130932556637999230067)
          ·
            refine ⟨55219696398834956998845101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36813130932556637999230067 55219696398834956998845101)
            ·
              refine ⟨20707386149563108874566913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55219696398834956998845101 20707386149563108874566913)
              ·
                refine ⟨15530539612172331655925185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20707386149563108874566913 15530539612172331655925185)
                ·
                  refine ⟨11647904709129248741943889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15530539612172331655925185 11647904709129248741943889)
                  ·
                    refine ⟨8735928531846936556457917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11647904709129248741943889 8735928531846936556457917)
                    ·
                      refine ⟨3275973199442601208671719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8735928531846936556457917 3275973199442601208671719)
                      ·
                        rfl

theorem cell23_6379935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_6379935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379935 prefixEnd_6379935 := by exact prefixLift 6379935
  have htrace : WordTrace (prefixWord ++ tailWord_6379935) baseStart_6379935 baseEnd_6379935 := by
    simpa [prefixWord, tailWord_6379935, baseEnd_6379935] using wordTrace_append hprefix tailTrace_6379935
  have hstable : (prefixWord ++ tailWord_6379935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379935).length < 2 ^ (prefixWord ++ tailWord_6379935).sum := by decide
  have hdescent : baseEnd_6379935 < baseStart_6379935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379938 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 8]
def baseStart_6379938 : Nat := 118140960795 + 6379938 * 2 ^ 59
def prefixEnd_6379938 : Nat := 4983230072969 + 3 ^ 40 * 6379938 * 2
def baseEnd_6379938 : Nat := 363997193320507188548245

theorem tailTrace_6379938 : CollatzResearch.WordTrace tailWord_6379938 prefixEnd_6379938 363997193320507188548245 := by
  unfold tailWord_6379938
  simp only [CollatzResearch.WordTrace]
  refine ⟨58173863890145426876873117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155130303707054471671661645 58173863890145426876873117)
  ·
    refine ⟨21815198958804535078827419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58173863890145426876873117 21815198958804535078827419)
    ·
      refine ⟨32722798438206802618241129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21815198958804535078827419 32722798438206802618241129)
      ·
        refine ⟨24542098828655101963680847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32722798438206802618241129 24542098828655101963680847)
        ·
          refine ⟨36813148242982652945521271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24542098828655101963680847 36813148242982652945521271)
          ·
            refine ⟨55219722364473979418281907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36813148242982652945521271 55219722364473979418281907)
            ·
              refine ⟨82829583546710969127422861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55219722364473979418281907 82829583546710969127422861)
              ·
                refine ⟨31061093830016613422783573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82829583546710969127422861 31061093830016613422783573)
                ·
                  refine ⟨363997193320507188548245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31061093830016613422783573 363997193320507188548245)
                  ·
                    rfl

theorem cell23_6379938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_6379938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379938 prefixEnd_6379938 := by exact prefixLift 6379938
  have htrace : WordTrace (prefixWord ++ tailWord_6379938) baseStart_6379938 baseEnd_6379938 := by
    simpa [prefixWord, tailWord_6379938, baseEnd_6379938] using wordTrace_append hprefix tailTrace_6379938
  have hstable : (prefixWord ++ tailWord_6379938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379938).length < 2 ^ (prefixWord ++ tailWord_6379938).sum := by decide
  have hdescent : baseEnd_6379938 < baseStart_6379938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379951 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 1, 11]
def baseStart_6379951 : Nat := 118140960795 + 6379951 * 2 ^ 59
def prefixEnd_6379951 : Nat := 4983230072969 + 3 ^ 40 * 6379951 * 2
def baseEnd_6379951 : Nat := 1091993805044357715357215

theorem tailTrace_6379951 : CollatzResearch.WordTrace tailWord_6379951 prefixEnd_6379951 1091993805044357715357215 := by
  unfold tailWord_6379951
  simp only [CollatzResearch.WordTrace]
  refine ⟨232695929709534610727715707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155130619806356407151810471 232695929709534610727715707)
  ·
    refine ⟨349043894564301916091573561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232695929709534610727715707 349043894564301916091573561)
    ·
      refine ⟨261782920923226437068680171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349043894564301916091573561 261782920923226437068680171)
      ·
        refine ⟨392674381384839655603020257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261782920923226437068680171 392674381384839655603020257)
        ·
          refine ⟨294505786038629741702265193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392674381384839655603020257 294505786038629741702265193)
          ·
            refine ⟨220879339528972306276698895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294505786038629741702265193 220879339528972306276698895)
            ·
              refine ⟨331319009293458459415048343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220879339528972306276698895 331319009293458459415048343)
              ·
                refine ⟨496978513940187689122572515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331319009293458459415048343 496978513940187689122572515)
                ·
                  refine ⟨745467770910281533683858773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 496978513940187689122572515 745467770910281533683858773)
                  ·
                    refine ⟨1091993805044357715357215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 745467770910281533683858773 1091993805044357715357215)
                    ·
                      rfl

theorem cell23_6379951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 11].length) (baseStart_6379951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379951 prefixEnd_6379951 := by exact prefixLift 6379951
  have htrace : WordTrace (prefixWord ++ tailWord_6379951) baseStart_6379951 baseEnd_6379951 := by
    simpa [prefixWord, tailWord_6379951, baseEnd_6379951] using wordTrace_append hprefix tailTrace_6379951
  have hstable : (prefixWord ++ tailWord_6379951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379951).length < 2 ^ (prefixWord ++ tailWord_6379951).sum := by decide
  have hdescent : baseEnd_6379951 < baseStart_6379951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6379999 : List Nat := [1, 1, 2, 3, 3, 3, 1, 4, 1, 1, 3]
def baseStart_6379999 : Nat := 118140960795 + 6379999 * 2 ^ 59
def prefixEnd_6379999 : Nat := 4983230072969 + 3 ^ 40 * 6379999 * 2
def baseEnd_6379999 : Nat := 3276006062204488958271425

theorem tailTrace_6379999 : CollatzResearch.WordTrace tailWord_6379999 prefixEnd_6379999 3276006062204488958271425 := by
  unfold tailWord_6379999
  simp only [CollatzResearch.WordTrace]
  refine ⟨232697680413360714925463051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155131786942240476616975367 232697680413360714925463051)
  ·
    refine ⟨349046520620041072388194577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232697680413360714925463051 349046520620041072388194577)
    ·
      refine ⟨261784890465030804291145933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349046520620041072388194577 261784890465030804291145933)
      ·
        refine ⟨98169333924386551609179725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261784890465030804291145933 98169333924386551609179725)
        ·
          refine ⟨36813500221644956853442397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98169333924386551609179725 36813500221644956853442397)
          ·
            refine ⟨13805062583116858820040899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36813500221644956853442397 13805062583116858820040899)
            ·
              refine ⟨20707593874675288230061349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13805062583116858820040899 20707593874675288230061349)
              ·
                refine ⟨3882673851501616543136503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20707593874675288230061349 3882673851501616543136503)
                ·
                  refine ⟨5824010777252424814704755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3882673851501616543136503 5824010777252424814704755)
                  ·
                    refine ⟨8736016165878637222057133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5824010777252424814704755 8736016165878637222057133)
                    ·
                      refine ⟨3276006062204488958271425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8736016165878637222057133 3276006062204488958271425)
                      ·
                        rfl

theorem cell23_6379999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 1, 1, 3].length) (baseStart_6379999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6379999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6379999 prefixEnd_6379999 := by exact prefixLift 6379999
  have htrace : WordTrace (prefixWord ++ tailWord_6379999) baseStart_6379999 baseEnd_6379999 := by
    simpa [prefixWord, tailWord_6379999, baseEnd_6379999] using wordTrace_append hprefix tailTrace_6379999
  have hstable : (prefixWord ++ tailWord_6379999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6379999).length < 2 ^ (prefixWord ++ tailWord_6379999).sum := by decide
  have hdescent : baseEnd_6379999 < baseStart_6379999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6379999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380022 : List Nat := [5, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4]
def baseStart_6380022 : Nat := 118140960795 + 6380022 * 2 ^ 59
def prefixEnd_6380022 : Nat := 4983230072969 + 3 ^ 40 * 6380022 * 2
def baseEnd_6380022 : Nat := 3276017872259542368283819

theorem tailTrace_6380022 : CollatzResearch.WordTrace tailWord_6380022 prefixEnd_6380022 3276017872259542368283819 := by
  unfold tailWord_6380022
  simp only [CollatzResearch.WordTrace]
  refine ⟨14543657455767336865846895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155132346194851593235700213 14543657455767336865846895)
  ·
    refine ⟨21815486183651005298770343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14543657455767336865846895 21815486183651005298770343)
    ·
      refine ⟨32723229275476507948155515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21815486183651005298770343 32723229275476507948155515)
      ·
        refine ⟨49084843913214761922233273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32723229275476507948155515 49084843913214761922233273)
        ·
          refine ⟨36813632934911071441674955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49084843913214761922233273 36813632934911071441674955)
          ·
            refine ⟨55220449402366607162512433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36813632934911071441674955 55220449402366607162512433)
            ·
              refine ⟨41415337051774955371884325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55220449402366607162512433 41415337051774955371884325)
              ·
                refine ⟨7765375697207804132228311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41415337051774955371884325 7765375697207804132228311)
                ·
                  refine ⟨11648063545811706198342467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7765375697207804132228311 11648063545811706198342467)
                  ·
                    refine ⟨17472095318717559297513701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11648063545811706198342467 17472095318717559297513701)
                    ·
                      refine ⟨3276017872259542368283819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17472095318717559297513701 3276017872259542368283819)
                      ·
                        rfl

theorem cell23_6380022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_6380022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380022 prefixEnd_6380022 := by exact prefixLift 6380022
  have htrace : WordTrace (prefixWord ++ tailWord_6380022) baseStart_6380022 baseEnd_6380022 := by
    simpa [prefixWord, tailWord_6380022, baseEnd_6380022] using wordTrace_append hprefix tailTrace_6380022
  have hstable : (prefixWord ++ tailWord_6380022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380022).length < 2 ^ (prefixWord ++ tailWord_6380022).sum := by decide
  have hdescent : baseEnd_6380022 < baseStart_6380022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380025 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 3, 2, 3]
def baseStart_6380025 : Nat := 118140960795 + 6380025 * 2 ^ 59
def prefixEnd_6380025 : Nat := 4983230072969 + 3 ^ 40 * 6380025 * 2
def baseEnd_6380025 : Nat := 3276019412701505856546305

theorem tailTrace_6380025 : CollatzResearch.WordTrace tailWord_6380025 prefixEnd_6380025 3276019412701505856546305 := by
  unfold tailWord_6380025
  simp only [CollatzResearch.WordTrace]
  refine ⟨232698628711266521365909529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155132419140844347577273019 232698628711266521365909529)
  ·
    refine ⟨174523971533449891024432147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232698628711266521365909529 174523971533449891024432147)
    ·
      refine ⟨261785957300174836536648221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174523971533449891024432147 261785957300174836536648221)
      ·
        refine ⟨98169733987565563701243083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261785957300174836536648221 98169733987565563701243083)
        ·
          refine ⟨147254600981348345551864625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98169733987565563701243083 147254600981348345551864625)
          ·
            refine ⟨110440950736011259163898469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147254600981348345551864625 110440950736011259163898469)
            ·
              refine ⟨20707678263002111093230963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110440950736011259163898469 20707678263002111093230963)
              ·
                refine ⟨31061517394503166639846445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20707678263002111093230963 31061517394503166639846445)
                ·
                  refine ⟨11648069022938687489942417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31061517394503166639846445 11648069022938687489942417)
                  ·
                    refine ⟨8736051767204015617456813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11648069022938687489942417 8736051767204015617456813)
                    ·
                      refine ⟨3276019412701505856546305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8736051767204015617456813 3276019412701505856546305)
                      ·
                        rfl

theorem cell23_6380025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_6380025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380025 prefixEnd_6380025 := by exact prefixLift 6380025
  have htrace : WordTrace (prefixWord ++ tailWord_6380025) baseStart_6380025 baseEnd_6380025 := by
    simpa [prefixWord, tailWord_6380025, baseEnd_6380025] using wordTrace_append hprefix tailTrace_6380025
  have hstable : (prefixWord ++ tailWord_6380025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380025).length < 2 ^ (prefixWord ++ tailWord_6380025).sum := by decide
  have hdescent : baseEnd_6380025 < baseStart_6380025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380042 : List Nat := [3, 1, 2, 2, 2, 1, 3, 3, 1, 2, 3]
def baseStart_6380042 : Nat := 118140960795 + 6380042 * 2 ^ 59
def prefixEnd_6380042 : Nat := 4983230072969 + 3 ^ 40 * 6380042 * 2
def baseEnd_6380042 : Nat := 3276028141872632290033727

theorem tailTrace_6380042 : CollatzResearch.WordTrace tailWord_6380042 prefixEnd_6380042 3276028141872632290033727 := by
  unfold tailWord_6380042
  simp only [CollatzResearch.WordTrace]
  refine ⟨58174812188051233317319595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155132832501469955512852253 58174812188051233317319595)
  ·
    refine ⟨87262218282076849975979393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58174812188051233317319595 87262218282076849975979393)
    ·
      refine ⟨65446663711557637481984545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87262218282076849975979393 65446663711557637481984545)
      ·
        refine ⟨49084997783668228111488409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65446663711557637481984545 49084997783668228111488409)
        ·
          refine ⟨36813748337751171083616307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49084997783668228111488409 36813748337751171083616307)
          ·
            refine ⟨55220622506626756625424461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36813748337751171083616307 55220622506626756625424461)
            ·
              refine ⟨20707733439985033734534173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55220622506626756625424461 20707733439985033734534173)
              ·
                refine ⟨7765400039994387650450315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20707733439985033734534173 7765400039994387650450315)
                ·
                  refine ⟨11648100059991581475675473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7765400039994387650450315 11648100059991581475675473)
                  ·
                    refine ⟨8736075044993686106756605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11648100059991581475675473 8736075044993686106756605)
                    ·
                      refine ⟨3276028141872632290033727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8736075044993686106756605 3276028141872632290033727)
                      ·
                        rfl

theorem cell23_6380042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_6380042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380042 prefixEnd_6380042 := by exact prefixLift 6380042
  have htrace : WordTrace (prefixWord ++ tailWord_6380042) baseStart_6380042 baseEnd_6380042 := by
    simpa [prefixWord, tailWord_6380042, baseEnd_6380042] using wordTrace_append hprefix tailTrace_6380042
  have hstable : (prefixWord ++ tailWord_6380042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380042).length < 2 ^ (prefixWord ++ tailWord_6380042).sum := by decide
  have hdescent : baseEnd_6380042 < baseStart_6380042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380056 : List Nat := [2, 1, 2, 3, 3, 1, 2, 4, 1, 2, 2]
def baseStart_6380056 : Nat := 118140960795 + 6380056 * 2 ^ 59
def prefixEnd_6380056 : Nat := 4983230072969 + 3 ^ 40 * 6380056 * 2
def baseEnd_6380056 : Nat := 3276035330601795235258663

theorem tailTrace_6380056 : CollatzResearch.WordTrace tailWord_6380056 prefixEnd_6380056 3276035330601795235258663 := by
  unfold tailWord_6380056
  simp only [CollatzResearch.WordTrace]
  refine ⟨116349879687077106830144011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155133172916102809106858681 116349879687077106830144011)
  ·
    refine ⟨174524819530615660245216017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116349879687077106830144011 174524819530615660245216017)
    ·
      refine ⟨130893614647961745183912013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174524819530615660245216017 130893614647961745183912013)
      ·
        refine ⟨49085105492985654443967005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130893614647961745183912013 49085105492985654443967005)
        ·
          refine ⟨18406914559869620416487627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49085105492985654443967005 18406914559869620416487627)
          ·
            refine ⟨27610371839804430624731441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18406914559869620416487627 27610371839804430624731441)
            ·
              refine ⟨20707778879853322968548581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27610371839804430624731441 20707778879853322968548581)
              ·
                refine ⟨3882708539972498056602859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20707778879853322968548581 3882708539972498056602859)
                ·
                  refine ⟨5824062809958747084904289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3882708539972498056602859 5824062809958747084904289)
                  ·
                    refine ⟨4368047107469060313678217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5824062809958747084904289 4368047107469060313678217)
                    ·
                      refine ⟨3276035330601795235258663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4368047107469060313678217 3276035330601795235258663)
                      ·
                        rfl

theorem cell23_6380056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_6380056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380056 prefixEnd_6380056 := by exact prefixLift 6380056
  have htrace : WordTrace (prefixWord ++ tailWord_6380056) baseStart_6380056 baseEnd_6380056 := by
    simpa [prefixWord, tailWord_6380056, baseEnd_6380056] using wordTrace_append hprefix tailTrace_6380056
  have hstable : (prefixWord ++ tailWord_6380056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380056).length < 2 ^ (prefixWord ++ tailWord_6380056).sum := by decide
  have hdescent : baseEnd_6380056 < baseStart_6380056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380058 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 1, 9]
def baseStart_6380058 : Nat := 118140960795 + 6380058 * 2 ^ 59
def prefixEnd_6380058 : Nat := 4983230072969 + 3 ^ 40 * 6380058 * 2
def baseEnd_6380058 : Nat := 1092012119187701409144551

theorem tailTrace_6380058 : CollatzResearch.WordTrace tailWord_6380058 prefixEnd_6380058 1092012119187701409144551 := by
  unfold tailWord_6380058
  simp only [CollatzResearch.WordTrace]
  refine ⟨58174958080036742000465207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155133221546764645334573885 58174958080036742000465207)
  ·
    refine ⟨87262437120055113000697811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58174958080036742000465207 87262437120055113000697811)
    ·
      refine ⟨130893655680082669501046717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87262437120055113000697811 130893655680082669501046717)
      ·
        refine ⟨49085120880031001062892519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130893655680082669501046717 49085120880031001062892519)
        ·
          refine ⟨73627681320046501594338779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49085120880031001062892519 73627681320046501594338779)
          ·
            refine ⟨110441521980069752391508169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73627681320046501594338779 110441521980069752391508169)
            ·
              refine ⟨82831141485052314293631127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110441521980069752391508169 82831141485052314293631127)
              ·
                refine ⟨124246712227578471440446691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82831141485052314293631127 124246712227578471440446691)
                ·
                  refine ⟨186370068341367707160670037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124246712227578471440446691 186370068341367707160670037)
                  ·
                    refine ⟨1092012119187701409144551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 186370068341367707160670037 1092012119187701409144551)
                    ·
                      rfl

theorem cell23_6380058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_6380058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380058 prefixEnd_6380058 := by exact prefixLift 6380058
  have htrace : WordTrace (prefixWord ++ tailWord_6380058) baseStart_6380058 baseEnd_6380058 := by
    simpa [prefixWord, tailWord_6380058, baseEnd_6380058] using wordTrace_append hprefix tailTrace_6380058
  have hstable : (prefixWord ++ tailWord_6380058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380058).length < 2 ^ (prefixWord ++ tailWord_6380058).sum := by decide
  have hdescent : baseEnd_6380058 < baseStart_6380058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380082 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2]
def baseStart_6380082 : Nat := 118140960795 + 6380082 * 2 ^ 59
def prefixEnd_6380082 : Nat := 4983230072969 + 3 ^ 40 * 6380082 * 2
def baseEnd_6380082 : Nat := 3276048681098812133533543

theorem tailTrace_6380082 : CollatzResearch.WordTrace tailWord_6380082 prefixEnd_6380082 3276048681098812133533543 := by
  unfold tailWord_6380082
  simp only [CollatzResearch.WordTrace]
  refine ⟨58175176918015005025183625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155133805114706680067156333 58175176918015005025183625)
  ·
    refine ⟨43631382688511253768887719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58175176918015005025183625 43631382688511253768887719)
    ·
      refine ⟨65447074032766880653331579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43631382688511253768887719 65447074032766880653331579)
      ·
        refine ⟨98170611049150320979997369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65447074032766880653331579 98170611049150320979997369)
        ·
          refine ⟨73627958286862740734998027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98170611049150320979997369 73627958286862740734998027)
          ·
            refine ⟨110441937430294111102497041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73627958286862740734998027 110441937430294111102497041)
            ·
              refine ⟨82831453072720583326872781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110441937430294111102497041 82831453072720583326872781)
              ·
                refine ⟨31061794902270218747577293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82831453072720583326872781 31061794902270218747577293)
                ·
                  refine ⟨11648173088351332030341485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31061794902270218747577293 11648173088351332030341485)
                  ·
                    refine ⟨4368064908131749511378057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11648173088351332030341485 4368064908131749511378057)
                    ·
                      refine ⟨3276048681098812133533543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4368064908131749511378057 3276048681098812133533543)
                      ·
                        rfl

theorem cell23_6380082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_6380082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380082 prefixEnd_6380082 := by exact prefixLift 6380082
  have htrace : WordTrace (prefixWord ++ tailWord_6380082) baseStart_6380082 baseEnd_6380082 := by
    simpa [prefixWord, tailWord_6380082, baseEnd_6380082] using wordTrace_append hprefix tailTrace_6380082
  have hstable : (prefixWord ++ tailWord_6380082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380082).length < 2 ^ (prefixWord ++ tailWord_6380082).sum := by decide
  have hdescent : baseEnd_6380082 < baseStart_6380082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380133 : List Nat := [1, 3, 1, 3, 5, 1, 1, 2, 1, 3, 2]
def baseStart_6380133 : Nat := 118140960795 + 6380133 * 2 ^ 59
def prefixEnd_6380133 : Nat := 4983230072969 + 3 ^ 40 * 6380133 * 2
def baseEnd_6380133 : Nat := 3276074868612191433995809

theorem tailTrace_6380133 : CollatzResearch.WordTrace tailWord_6380133 prefixEnd_6380133 3276074868612191433995809 := by
  unfold tailWord_6380133
  simp only [CollatzResearch.WordTrace]
  refine ⟨232702567794875255810841053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155135045196583503873894035 232702567794875255810841053)
  ·
    refine ⟨87263462923078220929065395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232702567794875255810841053 87263462923078220929065395)
    ·
      refine ⟨130895194384617331393598093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87263462923078220929065395 130895194384617331393598093)
      ·
        refine ⟨49085697894231499272599285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130895194384617331393598093 49085697894231499272599285)
        ·
          refine ⟨4601784177584203056806183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49085697894231499272599285 4601784177584203056806183)
          ·
            refine ⟨6902676266376304585209275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4601784177584203056806183 6902676266376304585209275)
            ·
              refine ⟨10354014399564456877813913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6902676266376304585209275 10354014399564456877813913)
              ·
                refine ⟨7765510799673342658360435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10354014399564456877813913 7765510799673342658360435)
                ·
                  refine ⟨11648266199510013987540653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7765510799673342658360435 11648266199510013987540653)
                  ·
                    refine ⟨4368099824816255245327745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11648266199510013987540653 4368099824816255245327745)
                    ·
                      refine ⟨3276074868612191433995809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4368099824816255245327745 3276074868612191433995809)
                      ·
                        rfl

theorem cell23_6380133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_6380133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380133 prefixEnd_6380133 := by exact prefixLift 6380133
  have htrace : WordTrace (prefixWord ++ tailWord_6380133) baseStart_6380133 baseEnd_6380133 := by
    simpa [prefixWord, tailWord_6380133, baseEnd_6380133] using wordTrace_append hprefix tailTrace_6380133
  have hstable : (prefixWord ++ tailWord_6380133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380133).length < 2 ^ (prefixWord ++ tailWord_6380133).sum := by decide
  have hdescent : baseEnd_6380133 < baseStart_6380133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380145 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 6, 3, 3]
def baseStart_6380145 : Nat := 118140960795 + 6380145 * 2 ^ 59
def prefixEnd_6380145 : Nat := 4983230072969 + 3 ^ 40 * 6380145 * 2
def baseEnd_6380145 : Nat := 3276081030380045387045753

theorem tailTrace_6380145 : CollatzResearch.WordTrace tailWord_6380145 prefixEnd_6380145 3276081030380045387045753 := by
  unfold tailWord_6380145
  simp only [CollatzResearch.WordTrace]
  refine ⟨232703005470831781860277889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155135336980554521240185259 232703005470831781860277889)
  ·
    refine ⟨174527254103123836395208417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232703005470831781860277889 174527254103123836395208417)
    ·
      refine ⟨130895440577342877296406313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174527254103123836395208417 130895440577342877296406313)
      ·
        refine ⟨98171580433007157972304735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130895440577342877296406313 98171580433007157972304735)
        ·
          refine ⟨147257370649510736958457103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98171580433007157972304735 147257370649510736958457103)
          ·
            refine ⟨220886055974266105437685655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147257370649510736958457103 220886055974266105437685655)
            ·
              refine ⟨331329083961399158156528483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220886055974266105437685655 331329083961399158156528483)
              ·
                refine ⟨496993625942098737234792725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331329083961399158156528483 496993625942098737234792725)
                ·
                  refine ⟨23296576216035878307880909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 496993625942098737234792725 23296576216035878307880909)
                  ·
                    refine ⟨8736216081013454365455341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23296576216035878307880909 8736216081013454365455341)
                    ·
                      refine ⟨3276081030380045387045753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8736216081013454365455341 3276081030380045387045753)
                      ·
                        rfl

theorem cell23_6380145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_6380145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380145 prefixEnd_6380145 := by exact prefixLift 6380145
  have htrace : WordTrace (prefixWord ++ tailWord_6380145) baseStart_6380145 baseEnd_6380145 := by
    simpa [prefixWord, tailWord_6380145, baseEnd_6380145] using wordTrace_append hprefix tailTrace_6380145
  have hstable : (prefixWord ++ tailWord_6380145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380145).length < 2 ^ (prefixWord ++ tailWord_6380145).sum := by decide
  have hdescent : baseEnd_6380145 < baseStart_6380145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380185 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 1, 3, 4]
def baseStart_6380185 : Nat := 118140960795 + 6380185 * 2 ^ 59
def prefixEnd_6380185 : Nat := 4983230072969 + 3 ^ 40 * 6380185 * 2
def baseEnd_6380185 : Nat := 3276101569606225230545569

theorem tailTrace_6380185 : CollatzResearch.WordTrace tailWord_6380185 prefixEnd_6380185 3276101569606225230545569 := by
  unfold tailWord_6380185
  simp only [CollatzResearch.WordTrace]
  refine ⟨232704464390686868691734009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155136309593791245794489339 232704464390686868691734009)
  ·
    refine ⟨174528348293015151518800507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232704464390686868691734009 174528348293015151518800507)
    ·
      refine ⟨261792522439522727278200761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174528348293015151518800507 261792522439522727278200761)
      ·
        refine ⟨196344391829642045458650571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261792522439522727278200761 196344391829642045458650571)
        ·
          refine ⟨294516587744463068187975857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196344391829642045458650571 294516587744463068187975857)
          ·
            refine ⟨220887440808347301140981893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294516587744463068187975857 220887440808347301140981893)
            ·
              refine ⟨41416395151565118963934105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 220887440808347301140981893 41416395151565118963934105)
              ·
                refine ⟨31062296363673839222950579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41416395151565118963934105 31062296363673839222950579)
                ·
                  refine ⟨46593444545510758834425869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31062296363673839222950579 46593444545510758834425869)
                  ·
                    refine ⟨17472541704566534562909701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46593444545510758834425869 17472541704566534562909701)
                    ·
                      refine ⟨3276101569606225230545569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17472541704566534562909701 3276101569606225230545569)
                      ·
                        rfl

theorem cell23_6380185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_6380185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380185 prefixEnd_6380185 := by exact prefixLift 6380185
  have htrace : WordTrace (prefixWord ++ tailWord_6380185) baseStart_6380185 baseEnd_6380185 := by
    simpa [prefixWord, tailWord_6380185, baseEnd_6380185] using wordTrace_append hprefix tailTrace_6380185
  have hstable : (prefixWord ++ tailWord_6380185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380185).length < 2 ^ (prefixWord ++ tailWord_6380185).sum := by decide
  have hdescent : baseEnd_6380185 < baseStart_6380185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380199 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 1, 7]
def baseStart_6380199 : Nat := 118140960795 + 6380199 * 2 ^ 59
def prefixEnd_6380199 : Nat := 4983230072969 + 3 ^ 40 * 6380199 * 2
def baseEnd_6380199 : Nat := 1092036252778462725256835

theorem tailTrace_6380199 : CollatzResearch.WordTrace tailWord_6380199 prefixEnd_6380199 1092036252778462725256835 := by
  unfold tailWord_6380199
  simp only [CollatzResearch.WordTrace]
  refine ⟨232704975012636149082743651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155136650008424099388495767 232704975012636149082743651)
  ·
    refine ⟨349057462518954223624115477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232704975012636149082743651 349057462518954223624115477)
    ·
      refine ⟨16362068555575979232380413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 349057462518954223624115477 16362068555575979232380413)
      ·
        refine ⟨6135775708340992212142655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16362068555575979232380413 6135775708340992212142655)
        ·
          refine ⟨9203663562511488318213983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6135775708340992212142655 9203663562511488318213983)
          ·
            refine ⟨13805495343767232477320975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9203663562511488318213983 13805495343767232477320975)
            ·
              refine ⟨20708243015650848715981463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13805495343767232477320975 20708243015650848715981463)
              ·
                refine ⟨31062364523476273073972195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20708243015650848715981463 31062364523476273073972195)
                ·
                  refine ⟨46593546785214409610958293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31062364523476273073972195 46593546785214409610958293)
                  ·
                    refine ⟨1092036252778462725256835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46593546785214409610958293 1092036252778462725256835)
                    ·
                      rfl

theorem cell23_6380199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_6380199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380199 prefixEnd_6380199 := by exact prefixLift 6380199
  have htrace : WordTrace (prefixWord ++ tailWord_6380199) baseStart_6380199 baseEnd_6380199 := by
    simpa [prefixWord, tailWord_6380199, baseEnd_6380199] using wordTrace_append hprefix tailTrace_6380199
  have hstable : (prefixWord ++ tailWord_6380199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380199).length < 2 ^ (prefixWord ++ tailWord_6380199).sum := by decide
  have hdescent : baseEnd_6380199 < baseStart_6380199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380272 : List Nat := [2, 1, 1, 1, 3, 1, 3, 5, 1, 5]
def baseStart_6380272 : Nat := 118140960795 + 6380272 * 2 ^ 59
def prefixEnd_6380272 : Nat := 4983230072969 + 3 ^ 40 * 6380272 * 2
def baseEnd_6380272 : Nat := 1092048747474388796719223

theorem tailTrace_6380272 : CollatzResearch.WordTrace tailWord_6380272 prefixEnd_6380272 1092048747474388796719223 := by
  unfold tailWord_6380272
  simp only [CollatzResearch.WordTrace]
  refine ⟨116353818770685841275075535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155138425027581121700100713 116353818770685841275075535)
  ·
    refine ⟨174530728156028761912613303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116353818770685841275075535 174530728156028761912613303)
    ·
      refine ⟨261796092234043142868919955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174530728156028761912613303 261796092234043142868919955)
      ·
        refine ⟨392694138351064714303379933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261796092234043142868919955 392694138351064714303379933)
        ·
          refine ⟨147260301881649267863767475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392694138351064714303379933 147260301881649267863767475)
          ·
            refine ⟨220890452822473901795651213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147260301881649267863767475 220890452822473901795651213)
            ·
              refine ⟨82833919808427713173369205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220890452822473901795651213 82833919808427713173369205)
              ·
                refine ⟨7765679982040098110003363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82833919808427713173369205 7765679982040098110003363)
                ·
                  refine ⟨11648519973060147165005045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7765679982040098110003363 11648519973060147165005045)
                  ·
                    refine ⟨1092048747474388796719223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11648519973060147165005045 1092048747474388796719223)
                    ·
                      rfl

theorem cell23_6380272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 1, 5].length) (baseStart_6380272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380272 prefixEnd_6380272 := by exact prefixLift 6380272
  have htrace : WordTrace (prefixWord ++ tailWord_6380272) baseStart_6380272 baseEnd_6380272 := by
    simpa [prefixWord, tailWord_6380272, baseEnd_6380272] using wordTrace_append hprefix tailTrace_6380272
  have hstable : (prefixWord ++ tailWord_6380272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380272).length < 2 ^ (prefixWord ++ tailWord_6380272).sum := by decide
  have hdescent : baseEnd_6380272 < baseStart_6380272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380302 : List Nat := [4, 1, 1, 2, 1, 1, 1, 5, 1, 6]
def baseStart_6380302 : Nat := 118140960795 + 6380302 * 2 ^ 59
def prefixEnd_6380302 : Nat := 4983230072969 + 3 ^ 40 * 6380302 * 2
def baseEnd_6380302 : Nat := 1092053882280933757594177

theorem tailTrace_6380302 : CollatzResearch.WordTrace tailWord_6380302 prefixEnd_6380302 1092053882280933757594177 := by
  unfold tailWord_6380302
  simp only [CollatzResearch.WordTrace]
  refine ⟨29088591466407874709217895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155139154487508665115828773 29088591466407874709217895)
  ·
    refine ⟨43632887199611812063826843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29088591466407874709217895 43632887199611812063826843)
    ·
      refine ⟨65449330799417718095740265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43632887199611812063826843 65449330799417718095740265)
      ·
        refine ⟨49086998099563288571805199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65449330799417718095740265 49086998099563288571805199)
        ·
          refine ⟨73630497149344932857707799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49086998099563288571805199 73630497149344932857707799)
          ·
            refine ⟨110445745724017399286561699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73630497149344932857707799 110445745724017399286561699)
            ·
              refine ⟨165668618586026098929842549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110445745724017399286561699 165668618586026098929842549)
              ·
                refine ⟨15531432992439946774672739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 165668618586026098929842549 15531432992439946774672739)
                ·
                  refine ⟨23297149488659920162009109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15531432992439946774672739 23297149488659920162009109)
                  ·
                    refine ⟨1092053882280933757594177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23297149488659920162009109 1092053882280933757594177)
                    ·
                      rfl

theorem cell23_6380302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_6380302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380302 prefixEnd_6380302 := by exact prefixLift 6380302
  have htrace : WordTrace (prefixWord ++ tailWord_6380302) baseStart_6380302 baseEnd_6380302 := by
    simpa [prefixWord, tailWord_6380302, baseEnd_6380302] using wordTrace_append hprefix tailTrace_6380302
  have hstable : (prefixWord ++ tailWord_6380302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380302).length < 2 ^ (prefixWord ++ tailWord_6380302).sum := by decide
  have hdescent : baseEnd_6380302 < baseStart_6380302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380306 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 3, 5]
def baseStart_6380306 : Nat := 118140960795 + 6380306 * 2 ^ 59
def prefixEnd_6380306 : Nat := 4983230072969 + 3 ^ 40 * 6380306 * 2
def baseEnd_6380306 : Nat := 1092054566921806419044171

theorem tailTrace_6380306 : CollatzResearch.WordTrace tailWord_6380306 prefixEnd_6380306 1092054566921806419044171 := by
  unfold tailWord_6380306
  simp only [CollatzResearch.WordTrace]
  refine ⟨58177219405812126589222193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155139251748832337571259181 58177219405812126589222193)
  ·
    refine ⟨43632914554359094941916645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58177219405812126589222193 43632914554359094941916645)
    ·
      refine ⟨8181171478942330301609371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43632914554359094941916645 8181171478942330301609371)
      ·
        refine ⟨12271757218413495452414057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8181171478942330301609371 12271757218413495452414057)
        ·
          refine ⟨9203817913810121589310543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12271757218413495452414057 9203817913810121589310543)
          ·
            refine ⟨13805726870715182383965815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9203817913810121589310543 13805726870715182383965815)
            ·
              refine ⟨20708590306072773575948723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13805726870715182383965815 20708590306072773575948723)
              ·
                refine ⟨31062885459109160363923085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20708590306072773575948723 31062885459109160363923085)
                ·
                  refine ⟨11648582047165935136471157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31062885459109160363923085 11648582047165935136471157)
                  ·
                    refine ⟨1092054566921806419044171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11648582047165935136471157 1092054566921806419044171)
                    ·
                      rfl

theorem cell23_6380306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_6380306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380306 prefixEnd_6380306 := by exact prefixLift 6380306
  have htrace : WordTrace (prefixWord ++ tailWord_6380306) baseStart_6380306 baseEnd_6380306 := by
    simpa [prefixWord, tailWord_6380306, baseEnd_6380306] using wordTrace_append hprefix tailTrace_6380306
  have hstable : (prefixWord ++ tailWord_6380306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380306).length < 2 ^ (prefixWord ++ tailWord_6380306).sum := by decide
  have hdescent : baseEnd_6380306 < baseStart_6380306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380343 : List Nat := [1, 1, 3, 1, 2, 1, 5, 4, 1, 2, 2]
def baseStart_6380343 : Nat := 118140960795 + 6380343 * 2 ^ 59
def prefixEnd_6380343 : Nat := 4983230072969 + 3 ^ 40 * 6380343 * 2
def baseEnd_6380343 : Nat := 3276182699549635612369843

theorem tailTrace_6380343 : CollatzResearch.WordTrace tailWord_6380343 prefixEnd_6380343 3276182699549635612369843 := by
  unfold tailWord_6380343
  simp only [CollatzResearch.WordTrace]
  refine ⟨232710227124114461675985683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155140151416076307783990455 232710227124114461675985683)
  ·
    refine ⟨349065340686171692513978525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232710227124114461675985683 349065340686171692513978525)
    ·
      refine ⟨130899502757314384692741947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349065340686171692513978525 130899502757314384692741947)
      ·
        refine ⟨196349254135971577039112921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130899502757314384692741947 196349254135971577039112921)
        ·
          refine ⟨147261940601978682779334691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196349254135971577039112921 147261940601978682779334691)
          ·
            refine ⟨220892910902968024169002037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147261940601978682779334691 220892910902968024169002037)
            ·
              refine ⟨20708710397153252265843941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 220892910902968024169002037 20708710397153252265843941)
              ·
                refine ⟨3882883199466234799845739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20708710397153252265843941 3882883199466234799845739)
                ·
                  refine ⟨5824324799199352199768609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3882883199466234799845739 5824324799199352199768609)
                  ·
                    refine ⟨4368243599399514149826457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5824324799199352199768609 4368243599399514149826457)
                    ·
                      refine ⟨3276182699549635612369843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4368243599399514149826457 3276182699549635612369843)
                      ·
                        rfl

theorem cell23_6380343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 1, 2, 2].length) (baseStart_6380343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380343 prefixEnd_6380343 := by exact prefixLift 6380343
  have htrace : WordTrace (prefixWord ++ tailWord_6380343) baseStart_6380343 baseEnd_6380343 := by
    simpa [prefixWord, tailWord_6380343, baseEnd_6380343] using wordTrace_append hprefix tailTrace_6380343
  have hstable : (prefixWord ++ tailWord_6380343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380343).length < 2 ^ (prefixWord ++ tailWord_6380343).sum := by decide
  have hdescent : baseEnd_6380343 < baseStart_6380343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380359 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 6, 1, 3]
def baseStart_6380359 : Nat := 118140960795 + 6380359 * 2 ^ 59
def prefixEnd_6380359 : Nat := 4983230072969 + 3 ^ 40 * 6380359 * 2
def baseEnd_6380359 : Nat := 3276190915240107549769769

theorem tailTrace_6380359 : CollatzResearch.WordTrace tailWord_6380359 prefixEnd_6380359 3276190915240107549769769 := by
  unfold tailWord_6380359
  simp only [CollatzResearch.WordTrace]
  refine ⟨232710810692056496408568131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155140540461370997605712087 232710810692056496408568131)
  ·
    refine ⟨349066216038084744612852197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232710810692056496408568131 349066216038084744612852197)
    ·
      refine ⟨65449915507140889614909787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 349066216038084744612852197 65449915507140889614909787)
      ·
        refine ⟨98174873260711334422364681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65449915507140889614909787 98174873260711334422364681)
        ·
          refine ⟨73631154945533500816773511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98174873260711334422364681 73631154945533500816773511)
          ·
            refine ⟨110446732418300251225160267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73631154945533500816773511 110446732418300251225160267)
            ·
              refine ⟨165670098627450376837740401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110446732418300251225160267 165670098627450376837740401)
              ·
                refine ⟨124252573970587782628305301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165670098627450376837740401 124252573970587782628305301)
                ·
                  refine ⟨5824339404871302310701811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124252573970587782628305301 5824339404871302310701811)
                  ·
                    refine ⟨8736509107306953466052717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5824339404871302310701811 8736509107306953466052717)
                    ·
                      refine ⟨3276190915240107549769769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8736509107306953466052717 3276190915240107549769769)
                      ·
                        rfl

theorem cell23_6380359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_6380359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380359 prefixEnd_6380359 := by exact prefixLift 6380359
  have htrace : WordTrace (prefixWord ++ tailWord_6380359) baseStart_6380359 baseEnd_6380359 := by
    simpa [prefixWord, tailWord_6380359, baseEnd_6380359] using wordTrace_append hprefix tailTrace_6380359
  have hstable : (prefixWord ++ tailWord_6380359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380359).length < 2 ^ (prefixWord ++ tailWord_6380359).sum := by decide
  have hdescent : baseEnd_6380359 < baseStart_6380359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380380 : List Nat := [2, 2, 4, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_6380380 : Nat := 118140960795 + 6380380 * 2 ^ 59
def prefixEnd_6380380 : Nat := 4983230072969 + 3 ^ 40 * 6380380 * 2
def baseEnd_6380380 : Nat := 3276201698333851967607173

theorem tailTrace_6380380 : CollatzResearch.WordTrace tailWord_6380380 prefixEnd_6380380 3276201698333851967607173 := by
  unfold tailWord_6380380
  simp only [CollatzResearch.WordTrace]
  refine ⟨116355788312490208497541297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155141051083320277996721729 116355788312490208497541297)
  ·
    refine ⟨87266841234367656373155973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116355788312490208497541297 87266841234367656373155973)
    ·
      refine ⟨16362532731443935569966745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87266841234367656373155973 16362532731443935569966745)
      ·
        refine ⟨12271899548582951677475059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16362532731443935569966745 12271899548582951677475059)
        ·
          refine ⟨18407849322874427516212589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12271899548582951677475059 18407849322874427516212589)
          ·
            refine ⟨6902943496077910318579721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18407849322874427516212589 6902943496077910318579721)
            ·
              refine ⟨5177207622058432738934791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6902943496077910318579721 5177207622058432738934791)
              ·
                refine ⟨7765811433087649108402187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5177207622058432738934791 7765811433087649108402187)
                ·
                  refine ⟨11648717149631473662603281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7765811433087649108402187 11648717149631473662603281)
                  ·
                    refine ⟨8736537862223605246952461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11648717149631473662603281 8736537862223605246952461)
                    ·
                      refine ⟨3276201698333851967607173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8736537862223605246952461 3276201698333851967607173)
                      ·
                        rfl

theorem cell23_6380380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_6380380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380380 prefixEnd_6380380 := by exact prefixLift 6380380
  have htrace : WordTrace (prefixWord ++ tailWord_6380380) baseStart_6380380 baseEnd_6380380 := by
    simpa [prefixWord, tailWord_6380380, baseEnd_6380380] using wordTrace_append hprefix tailTrace_6380380
  have hstable : (prefixWord ++ tailWord_6380380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380380).length < 2 ^ (prefixWord ++ tailWord_6380380).sum := by decide
  have hdescent : baseEnd_6380380 < baseStart_6380380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380399 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 3, 4, 2]
def baseStart_6380399 : Nat := 118140960795 + 6380399 * 2 ^ 59
def prefixEnd_6380399 : Nat := 4983230072969 + 3 ^ 40 * 6380399 * 2
def baseEnd_6380399 : Nat := 3276211454466287393269585

theorem tailTrace_6380399 : CollatzResearch.WordTrace tailWord_6380399 prefixEnd_6380399 3276211454466287393269585 := by
  unfold tailWord_6380399
  simp only [CollatzResearch.WordTrace]
  refine ⟨232712269611911583240024251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155141513074607722160016167 232712269611911583240024251)
  ·
    refine ⟨349068404417867374860036377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232712269611911583240024251 349068404417867374860036377)
    ·
      refine ⟨261801303313400531145027283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349068404417867374860036377 261801303313400531145027283)
      ·
        refine ⟨392701954970100796717540925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261801303313400531145027283 392701954970100796717540925)
        ·
          refine ⟨147263233113787798769077847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392701954970100796717540925 147263233113787798769077847)
          ·
            refine ⟨220894849670681698153616771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147263233113787798769077847 220894849670681698153616771)
            ·
              refine ⟨331342274506022547230425157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220894849670681698153616771 331342274506022547230425157)
              ·
                refine ⟨62126676469879227605704717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 331342274506022547230425157 62126676469879227605704717)
                ·
                  refine ⟨23297503676204710352139269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62126676469879227605704717 23297503676204710352139269)
                  ·
                    refine ⟨4368281939288383191026113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23297503676204710352139269 4368281939288383191026113)
                    ·
                      refine ⟨3276211454466287393269585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4368281939288383191026113 3276211454466287393269585)
                      ·
                        rfl

theorem cell23_6380399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 4, 2].length) (baseStart_6380399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380399 prefixEnd_6380399 := by exact prefixLift 6380399
  have htrace : WordTrace (prefixWord ++ tailWord_6380399) baseStart_6380399 baseEnd_6380399 := by
    simpa [prefixWord, tailWord_6380399, baseEnd_6380399] using wordTrace_append hprefix tailTrace_6380399
  have hstable : (prefixWord ++ tailWord_6380399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380399).length < 2 ^ (prefixWord ++ tailWord_6380399).sum := by decide
  have hdescent : baseEnd_6380399 < baseStart_6380399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380459 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 1, 7, 2]
def baseStart_6380459 : Nat := 118140960795 + 6380459 * 2 ^ 59
def prefixEnd_6380459 : Nat := 4983230072969 + 3 ^ 40 * 6380459 * 2
def baseEnd_6380459 : Nat := 3276242263305557158519309

theorem tailTrace_6380459 : CollatzResearch.WordTrace tailWord_6380459 prefixEnd_6380459 3276242263305557158519309 := by
  unfold tailWord_6380459
  simp only [CollatzResearch.WordTrace]
  refine ⟨232714457991694213487208431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155142971994462808991472287 232714457991694213487208431)
  ·
    refine ⟨349071686987541320230812647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232714457991694213487208431 349071686987541320230812647)
    ·
      refine ⟨523607530481311980346218971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349071686987541320230812647 523607530481311980346218971)
      ·
        refine ⟨785411295721967970519328457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523607530481311980346218971 785411295721967970519328457)
        ·
          refine ⟨589058471791475977889496343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 785411295721967970519328457 589058471791475977889496343)
          ·
            refine ⟨883587707687213966834244515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589058471791475977889496343 883587707687213966834244515)
            ·
              refine ⟨1325381561530820950251366773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883587707687213966834244515 1325381561530820950251366773)
              ·
                refine ⟨124254521393514464086065635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1325381561530820950251366773 124254521393514464086065635)
                ·
                  refine ⟨186381782090271696129098453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124254521393514464086065635 186381782090271696129098453)
                  ·
                    refine ⟨4368323017740742878025745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 186381782090271696129098453 4368323017740742878025745)
                    ·
                      refine ⟨3276242263305557158519309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4368323017740742878025745 3276242263305557158519309)
                      ·
                        rfl

theorem cell23_6380459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 7, 2].length) (baseStart_6380459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380459 prefixEnd_6380459 := by exact prefixLift 6380459
  have htrace : WordTrace (prefixWord ++ tailWord_6380459) baseStart_6380459 baseEnd_6380459 := by
    simpa [prefixWord, tailWord_6380459, baseEnd_6380459] using wordTrace_append hprefix tailTrace_6380459
  have hstable : (prefixWord ++ tailWord_6380459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380459).length < 2 ^ (prefixWord ++ tailWord_6380459).sum := by decide
  have hdescent : baseEnd_6380459 < baseStart_6380459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380469 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 4, 5]
def baseStart_6380469 : Nat := 118140960795 + 6380469 * 2 ^ 59
def prefixEnd_6380469 : Nat := 4983230072969 + 3 ^ 40 * 6380469 * 2
def baseEnd_6380469 : Nat := 1092082466037367373131421

theorem tailTrace_6380469 : CollatzResearch.WordTrace tailWord_6380469 prefixEnd_6380469 1092082466037367373131421 := by
  unfold tailWord_6380469
  simp only [CollatzResearch.WordTrace]
  refine ⟨232714822721657985195072461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155143215147771990130048307 232714822721657985195072461)
  ·
    refine ⟨87268058520621744448152173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232714822721657985195072461 87268058520621744448152173)
    ·
      refine ⟨32725521945233154168057065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87268058520621744448152173 32725521945233154168057065)
      ·
        refine ⟨24544141458924865626042799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32725521945233154168057065 24544141458924865626042799)
        ·
          refine ⟨36816212188387298439064199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24544141458924865626042799 36816212188387298439064199)
          ·
            refine ⟨55224318282580947658596299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36816212188387298439064199 55224318282580947658596299)
            ·
              refine ⟨82836477423871421487894449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55224318282580947658596299 82836477423871421487894449)
              ·
                refine ⟨62127358067903566115920837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82836477423871421487894449 62127358067903566115920837)
                ·
                  refine ⟨11648879637731918646735157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62127358067903566115920837 11648879637731918646735157)
                  ·
                    refine ⟨1092082466037367373131421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11648879637731918646735157 1092082466037367373131421)
                    ·
                      rfl

theorem cell23_6380469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_6380469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380469 prefixEnd_6380469 := by exact prefixLift 6380469
  have htrace : WordTrace (prefixWord ++ tailWord_6380469) baseStart_6380469 baseEnd_6380469 := by
    simpa [prefixWord, tailWord_6380469, baseEnd_6380469] using wordTrace_append hprefix tailTrace_6380469
  have hstable : (prefixWord ++ tailWord_6380469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380469).length < 2 ^ (prefixWord ++ tailWord_6380469).sum := by decide
  have hdescent : baseEnd_6380469 < baseStart_6380469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380506 : List Nat := [3, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4]
def baseStart_6380506 : Nat := 118140960795 + 6380506 * 2 ^ 59
def prefixEnd_6380506 : Nat := 4983230072969 + 3 ^ 40 * 6380506 * 2
def baseEnd_6380506 : Nat := 3276266396896318474631593

theorem tailTrace_6380506 : CollatzResearch.WordTrace tailWord_6380506 prefixEnd_6380506 3276266396896318474631593 := by
  unfold tailWord_6380506
  simp only [CollatzResearch.WordTrace]
  refine ⟨58179043055630985128542343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155144114815015960342779581 58179043055630985128542343)
  ·
    refine ⟨87268564583446477692813515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58179043055630985128542343 87268564583446477692813515)
    ·
      refine ⟨130902846875169716539220273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87268564583446477692813515 130902846875169716539220273)
      ·
        refine ⟨98177135156377287404415205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130902846875169716539220273 98177135156377287404415205)
        ·
          refine ⟨18408212841820741388327851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98177135156377287404415205 18408212841820741388327851)
          ·
            refine ⟨27612319262731112082491777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18408212841820741388327851 27612319262731112082491777)
            ·
              refine ⟨20709239447048334061868833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27612319262731112082491777 20709239447048334061868833)
              ·
                refine ⟨15531929585286250546401625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20709239447048334061868833 15531929585286250546401625)
                ·
                  refine ⟨11648947188964687909801219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15531929585286250546401625 11648947188964687909801219)
                  ·
                    refine ⟨17473420783447031864701829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11648947188964687909801219 17473420783447031864701829)
                    ·
                      refine ⟨3276266396896318474631593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17473420783447031864701829 3276266396896318474631593)
                      ·
                        rfl

theorem cell23_6380506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_6380506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380506 prefixEnd_6380506 := by exact prefixLift 6380506
  have htrace : WordTrace (prefixWord ++ tailWord_6380506) baseStart_6380506 baseEnd_6380506 := by
    simpa [prefixWord, tailWord_6380506, baseEnd_6380506] using wordTrace_append hprefix tailTrace_6380506
  have hstable : (prefixWord ++ tailWord_6380506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380506).length < 2 ^ (prefixWord ++ tailWord_6380506).sum := by decide
  have hdescent : baseEnd_6380506 < baseStart_6380506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380599 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 5]
def baseStart_6380599 : Nat := 118140960795 + 6380599 * 2 ^ 59
def prefixEnd_6380599 : Nat := 4983230072969 + 3 ^ 40 * 6380599 * 2
def baseEnd_6380599 : Nat := 3276314150597186610768665

theorem tailTrace_6380599 : CollatzResearch.WordTrace tailWord_6380599 prefixEnd_6380599 3276314150597186610768665 := by
  unfold tailWord_6380599
  simp only [CollatzResearch.WordTrace]
  refine ⟨232719564211187017397304851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155146376140791344931536567 232719564211187017397304851)
  ·
    refine ⟨349079346316780526095957277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232719564211187017397304851 349079346316780526095957277)
    ·
      refine ⟨130904754868792697285983979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349079346316780526095957277 130904754868792697285983979)
      ·
        refine ⟨196357132303189045928975969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130904754868792697285983979 196357132303189045928975969)
        ·
          refine ⟨147267849227391784446731977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196357132303189045928975969 147267849227391784446731977)
          ·
            refine ⟨110450886920543838335048983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147267849227391784446731977 110450886920543838335048983)
            ·
              refine ⟨165676330380815757502573475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110450886920543838335048983 165676330380815757502573475)
              ·
                refine ⟨248514495571223636253860213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165676330380815757502573475 248514495571223636253860213)
                ·
                  refine ⟨23298233959802215898799395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 248514495571223636253860213 23298233959802215898799395)
                  ·
                    refine ⟨34947350939703323848199093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23298233959802215898799395 34947350939703323848199093)
                    ·
                      refine ⟨3276314150597186610768665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34947350939703323848199093 3276314150597186610768665)
                      ·
                        rfl

theorem cell23_6380599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_6380599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380599 prefixEnd_6380599 := by exact prefixLift 6380599
  have htrace : WordTrace (prefixWord ++ tailWord_6380599) baseStart_6380599 baseEnd_6380599 := by
    simpa [prefixWord, tailWord_6380599, baseEnd_6380599] using wordTrace_append hprefix tailTrace_6380599
  have hstable : (prefixWord ++ tailWord_6380599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380599).length < 2 ^ (prefixWord ++ tailWord_6380599).sum := by decide
  have hdescent : baseEnd_6380599 < baseStart_6380599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380613 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 5, 2, 2]
def baseStart_6380613 : Nat := 118140960795 + 6380613 * 2 ^ 59
def prefixEnd_6380613 : Nat := 4983230072969 + 3 ^ 40 * 6380613 * 2
def baseEnd_6380613 : Nat := 3276321339326349555993601

theorem tailTrace_6380613 : CollatzResearch.WordTrace tailWord_6380613 prefixEnd_6380613 3276321339326349555993601 := by
  unfold tailWord_6380613
  simp only [CollatzResearch.WordTrace]
  refine ⟨232720074833136297788314493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155146716555424198525542995 232720074833136297788314493)
  ·
    refine ⟨87270028062426111670617935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232720074833136297788314493 87270028062426111670617935)
    ·
      refine ⟨130905042093639167505926903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87270028062426111670617935 130905042093639167505926903)
      ·
        refine ⟨196357563140458751258890355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130905042093639167505926903 196357563140458751258890355)
        ·
          refine ⟨294536344710688126888335533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196357563140458751258890355 294536344710688126888335533)
          ·
            refine ⟨110451129266508047583125825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294536344710688126888335533 110451129266508047583125825)
            ·
              refine ⟨82838346949881035687344369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110451129266508047583125825 82838346949881035687344369)
              ·
                refine ⟨62128760212410776765508277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82838346949881035687344369 62128760212410776765508277)
                ·
                  refine ⟨5824571269913510321766401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62128760212410776765508277 5824571269913510321766401)
                  ·
                    refine ⟨4368428452435132741324801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5824571269913510321766401 4368428452435132741324801)
                    ·
                      refine ⟨3276321339326349555993601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4368428452435132741324801 3276321339326349555993601)
                      ·
                        rfl

theorem cell23_6380613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 2, 2].length) (baseStart_6380613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380613 prefixEnd_6380613 := by exact prefixLift 6380613
  have htrace : WordTrace (prefixWord ++ tailWord_6380613) baseStart_6380613 baseEnd_6380613 := by
    simpa [prefixWord, tailWord_6380613, baseEnd_6380613] using wordTrace_append hprefix tailTrace_6380613
  have hstable : (prefixWord ++ tailWord_6380613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380613).length < 2 ^ (prefixWord ++ tailWord_6380613).sum := by decide
  have hdescent : baseEnd_6380613 < baseStart_6380613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380616 : List Nat := [2, 1, 3, 1, 1, 1, 6, 1, 1, 1, 5]
def baseStart_6380616 : Nat := 118140960795 + 6380616 * 2 ^ 59
def prefixEnd_6380616 : Nat := 4983230072969 + 3 ^ 40 * 6380616 * 2
def baseEnd_6380616 : Nat := 3276322879768313044256087

theorem tailTrace_6380616 : CollatzResearch.WordTrace tailWord_6380616 prefixEnd_6380616 3276322879768313044256087 := by
  unfold tailWord_6380616
  simp only [CollatzResearch.WordTrace]
  refine ⟨116360092126062714650336851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155146789501416952867115801 116360092126062714650336851)
  ·
    refine ⟨174540138189094071975505277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116360092126062714650336851 174540138189094071975505277)
    ·
      refine ⟨65452551820910276990814479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174540138189094071975505277 65452551820910276990814479)
      ·
        refine ⟨98178827731365415486221719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65452551820910276990814479 98178827731365415486221719)
        ·
          refine ⟨147268241597048123229332579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98178827731365415486221719 147268241597048123229332579)
          ·
            refine ⟨220902362395572184843998869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147268241597048123229332579 220902362395572184843998869)
            ·
              refine ⟨10354798237292446164562447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 220902362395572184843998869 10354798237292446164562447)
              ·
                refine ⟨15532197355938669246843671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10354798237292446164562447 15532197355938669246843671)
                ·
                  refine ⟨23298296033908003870265507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15532197355938669246843671 23298296033908003870265507)
                  ·
                    refine ⟨34947444050862005805398261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23298296033908003870265507 34947444050862005805398261)
                    ·
                      refine ⟨3276322879768313044256087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34947444050862005805398261 3276322879768313044256087)
                      ·
                        rfl

theorem cell23_6380616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_6380616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380616 prefixEnd_6380616 := by exact prefixLift 6380616
  have htrace : WordTrace (prefixWord ++ tailWord_6380616) baseStart_6380616 baseEnd_6380616 := by
    simpa [prefixWord, tailWord_6380616, baseEnd_6380616] using wordTrace_append hprefix tailTrace_6380616
  have hstable : (prefixWord ++ tailWord_6380616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380616).length < 2 ^ (prefixWord ++ tailWord_6380616).sum := by decide
  have hdescent : baseEnd_6380616 < baseStart_6380616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380626 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_6380626 : Nat := 118140960795 + 6380626 * 2 ^ 59
def prefixEnd_6380626 : Nat := 4983230072969 + 3 ^ 40 * 6380626 * 2
def baseEnd_6380626 : Nat := 3276328014574858005131041

theorem tailTrace_6380626 : CollatzResearch.WordTrace tailWord_6380626 prefixEnd_6380626 3276328014574858005131041 := by
  unfold tailWord_6380626
  simp only [CollatzResearch.WordTrace]
  refine ⟨58180137245522300252134433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155147032654726134005691821 58180137245522300252134433)
  ·
    refine ⟨43635102934141725189100825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58180137245522300252134433 43635102934141725189100825)
    ·
      refine ⟨32726327200606293891825619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43635102934141725189100825 32726327200606293891825619)
      ·
        refine ⟨49089490800909440837738429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32726327200606293891825619 49089490800909440837738429)
        ·
          refine ⟨18408559050341040314151911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49089490800909440837738429 18408559050341040314151911)
          ·
            refine ⟨27612838575511560471227867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18408559050341040314151911 27612838575511560471227867)
            ·
              refine ⟨41419257863267340706841801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27612838575511560471227867 41419257863267340706841801)
              ·
                refine ⟨31064443397450505530131351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41419257863267340706841801 31064443397450505530131351)
                ·
                  refine ⟨46596665096175758295197027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31064443397450505530131351 46596665096175758295197027)
                  ·
                    refine ⟨69894997644263637442795541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46596665096175758295197027 69894997644263637442795541)
                    ·
                      refine ⟨3276328014574858005131041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69894997644263637442795541 3276328014574858005131041)
                      ·
                        rfl

theorem cell23_6380626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_6380626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380626 prefixEnd_6380626 := by exact prefixLift 6380626
  have htrace : WordTrace (prefixWord ++ tailWord_6380626) baseStart_6380626 baseEnd_6380626 := by
    simpa [prefixWord, tailWord_6380626, baseEnd_6380626] using wordTrace_append hprefix tailTrace_6380626
  have hstable : (prefixWord ++ tailWord_6380626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380626).length < 2 ^ (prefixWord ++ tailWord_6380626).sum := by decide
  have hdescent : baseEnd_6380626 < baseStart_6380626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380636 : List Nat := [2, 2, 4, 1, 1, 1, 4, 8]
def baseStart_6380636 : Nat := 118140960795 + 6380636 * 2 ^ 59
def prefixEnd_6380636 : Nat := 4983230072969 + 3 ^ 40 * 6380636 * 2
def baseEnd_6380636 : Nat := 121345672199311220963185

theorem tailTrace_6380636 : CollatzResearch.WordTrace tailWord_6380636 prefixEnd_6380636 121345672199311220963185 := by
  unfold tailWord_6380636
  simp only [CollatzResearch.WordTrace]
  refine ⟨116360456856026486358200881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155147275808035315144267841 116360456856026486358200881)
  ·
    refine ⟨87270342642019864768650661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116360456856026486358200881 87270342642019864768650661)
    ·
      refine ⟨16363189245378724644121999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87270342642019864768650661 16363189245378724644121999)
      ·
        refine ⟨24544783868068086966182999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16363189245378724644121999 24544783868068086966182999)
        ·
          refine ⟨36817175802102130449274499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24544783868068086966182999 36817175802102130449274499)
          ·
            refine ⟨55225763703153195673911749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36817175802102130449274499 55225763703153195673911749)
            ·
              refine ⟨10354830694341224188858453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55225763703153195673911749 10354830694341224188858453)
              ·
                refine ⟨121345672199311220963185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10354830694341224188858453 121345672199311220963185)
                ·
                  rfl

theorem cell23_6380636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 8].length) (baseStart_6380636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380636 prefixEnd_6380636 := by exact prefixLift 6380636
  have htrace : WordTrace (prefixWord ++ tailWord_6380636) baseStart_6380636 baseEnd_6380636 := by
    simpa [prefixWord, tailWord_6380636, baseEnd_6380636] using wordTrace_append hprefix tailTrace_6380636
  have hstable : (prefixWord ++ tailWord_6380636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380636).length < 2 ^ (prefixWord ++ tailWord_6380636).sum := by decide
  have hdescent : baseEnd_6380636 < baseStart_6380636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380639 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 6]
def baseStart_6380639 : Nat := 118140960795 + 6380639 * 2 ^ 59
def prefixEnd_6380639 : Nat := 4983230072969 + 3 ^ 40 * 6380639 * 2
def baseEnd_6380639 : Nat := 3276334689823366454268481

theorem tailTrace_6380639 : CollatzResearch.WordTrace tailWord_6380639 prefixEnd_6380639 3276334689823366454268481 := by
  unfold tailWord_6380639
  simp only [CollatzResearch.WordTrace]
  refine ⟨232721023131042104228760971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155147348754028069485840647 232721023131042104228760971)
  ·
    refine ⟨349081534696563156343141457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232721023131042104228760971 349081534696563156343141457)
    ·
      refine ⟨261811151022422367257356093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349081534696563156343141457 261811151022422367257356093)
      ·
        refine ⟨98179181633408387721508535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261811151022422367257356093 98179181633408387721508535)
        ·
          refine ⟨147268772450112581582262803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98179181633408387721508535 147268772450112581582262803)
          ·
            refine ⟨220903158675168872373394205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147268772450112581582262803 220903158675168872373394205)
            ·
              refine ⟨82838684503188327140022827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220903158675168872373394205 82838684503188327140022827)
              ·
                refine ⟨124258026754782490710034241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82838684503188327140022827 124258026754782490710034241)
                ·
                  refine ⟨93193520066086868032525681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124258026754782490710034241 93193520066086868032525681)
                  ·
                    refine ⟨69895140049565151024394261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93193520066086868032525681 69895140049565151024394261)
                    ·
                      refine ⟨3276334689823366454268481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69895140049565151024394261 3276334689823366454268481)
                      ·
                        rfl

theorem cell23_6380639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_6380639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380639 prefixEnd_6380639 := by exact prefixLift 6380639
  have htrace : WordTrace (prefixWord ++ tailWord_6380639) baseStart_6380639 baseEnd_6380639 := by
    simpa [prefixWord, tailWord_6380639, baseEnd_6380639] using wordTrace_append hprefix tailTrace_6380639
  have hstable : (prefixWord ++ tailWord_6380639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380639).length < 2 ^ (prefixWord ++ tailWord_6380639).sum := by decide
  have hdescent : baseEnd_6380639 < baseStart_6380639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380650 : List Nat := [3, 1, 3, 2, 2, 1, 3, 2, 1, 2, 3]
def baseStart_6380650 : Nat := 118140960795 + 6380650 * 2 ^ 59
def prefixEnd_6380650 : Nat := 4983230072969 + 3 ^ 40 * 6380650 * 2
def baseEnd_6380650 : Nat := 3276340338110565911230931

theorem tailTrace_6380650 : CollatzResearch.WordTrace tailWord_6380650 prefixEnd_6380650 3276340338110565911230931 := by
  unfold tailWord_6380650
  simp only [CollatzResearch.WordTrace]
  refine ⟨58180356083500563276852851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155147616222668168738274269 58180356083500563276852851)
  ·
    refine ⟨87270534125250844915279277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58180356083500563276852851 87270534125250844915279277)
    ·
      refine ⟨32726450296969066843229729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87270534125250844915279277 32726450296969066843229729)
      ·
        refine ⟨24544837722726800132422297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32726450296969066843229729 24544837722726800132422297)
        ·
          refine ⟨18408628292045100099316723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24544837722726800132422297 18408628292045100099316723)
          ·
            refine ⟨27612942438067650148975085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18408628292045100099316723 27612942438067650148975085)
            ·
              refine ⟨10354853414275368805865657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27612942438067650148975085 10354853414275368805865657)
              ·
                refine ⟨7766140060706526604399243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10354853414275368805865657 7766140060706526604399243)
                ·
                  refine ⟨11649210091059789906598865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7766140060706526604399243 11649210091059789906598865)
                  ·
                    refine ⟨8736907568294842429949149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11649210091059789906598865 8736907568294842429949149)
                    ·
                      refine ⟨3276340338110565911230931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8736907568294842429949149 3276340338110565911230931)
                      ·
                        rfl

theorem cell23_6380650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_6380650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380650 prefixEnd_6380650 := by exact prefixLift 6380650
  have htrace : WordTrace (prefixWord ++ tailWord_6380650) baseStart_6380650 baseEnd_6380650 := by
    simpa [prefixWord, tailWord_6380650, baseEnd_6380650] using wordTrace_append hprefix tailTrace_6380650
  have hstable : (prefixWord ++ tailWord_6380650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380650).length < 2 ^ (prefixWord ++ tailWord_6380650).sum := by decide
  have hdescent : baseEnd_6380650 < baseStart_6380650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380670 : List Nat := [4, 2, 4, 1, 1, 11]
def baseStart_6380670 : Nat := 118140960795 + 6380670 * 2 ^ 59
def prefixEnd_6380670 : Nat := 4983230072969 + 3 ^ 40 * 6380670 * 2
def baseEnd_6380670 : Nat := 13482924311619982851773

theorem tailTrace_6380670 : CollatzResearch.WordTrace tailWord_6380670 prefixEnd_6380670 13482924311619982851773 := by
  unfold tailWord_6380670
  simp only [CollatzResearch.WordTrace]
  refine ⟨29090269224241224565392433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155148102529286531015426309 29090269224241224565392433)
  ·
    refine ⟨21817701918180918424044325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29090269224241224565392433 21817701918180918424044325)
    ·
      refine ⟨4090819109658922204508311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21817701918180918424044325 4090819109658922204508311)
      ·
        refine ⟨6136228664488383306762467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4090819109658922204508311 6136228664488383306762467)
        ·
          refine ⟨9204342996732574960143701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6136228664488383306762467 9204342996732574960143701)
          ·
            refine ⟨13482924311619982851773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9204342996732574960143701 13482924311619982851773)
            ·
              rfl

theorem cell23_6380670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 11].length) (baseStart_6380670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380670 prefixEnd_6380670 := by exact prefixLift 6380670
  have htrace : WordTrace (prefixWord ++ tailWord_6380670) baseStart_6380670 baseEnd_6380670 := by
    simpa [prefixWord, tailWord_6380670, baseEnd_6380670] using wordTrace_append hprefix tailTrace_6380670
  have hstable : (prefixWord ++ tailWord_6380670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380670).length < 2 ^ (prefixWord ++ tailWord_6380670).sum := by decide
  have hdescent : baseEnd_6380670 < baseStart_6380670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380690 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_6380690 : Nat := 118140960795 + 6380690 * 2 ^ 59
def prefixEnd_6380690 : Nat := 4983230072969 + 3 ^ 40 * 6380690 * 2
def baseEnd_6380690 : Nat := 3276360877336745754730747

theorem tailTrace_6380690 : CollatzResearch.WordTrace tailWord_6380690 prefixEnd_6380690 3276360877336745754730747 := by
  unfold tailWord_6380690
  simp only [CollatzResearch.WordTrace]
  refine ⟨58180720813464334984716881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155148588835904893292578349 58180720813464334984716881)
  ·
    refine ⟨43635540610098251238537661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58180720813464334984716881 43635540610098251238537661)
    ·
      refine ⟨16363327728786844214451623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43635540610098251238537661 16363327728786844214451623)
      ·
        refine ⟨24544991593180266321677435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16363327728786844214451623 24544991593180266321677435)
        ·
          refine ⟨36817487389770399482516153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24544991593180266321677435 36817487389770399482516153)
          ·
            refine ⟨27613115542327799611887115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36817487389770399482516153 27613115542327799611887115)
            ·
              refine ⟨41419673313491699417830673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27613115542327799611887115 41419673313491699417830673)
              ·
                refine ⟨31064754985118774563373005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41419673313491699417830673 31064754985118774563373005)
                ·
                  refine ⟨11649283119419540461264877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31064754985118774563373005 11649283119419540461264877)
                  ·
                    refine ⟨4368481169782327672974329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11649283119419540461264877 4368481169782327672974329)
                    ·
                      refine ⟨3276360877336745754730747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4368481169782327672974329 3276360877336745754730747)
                      ·
                        rfl

theorem cell23_6380690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_6380690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380690 prefixEnd_6380690 := by exact prefixLift 6380690
  have htrace : WordTrace (prefixWord ++ tailWord_6380690) baseStart_6380690 baseEnd_6380690 := by
    simpa [prefixWord, tailWord_6380690, baseEnd_6380690] using wordTrace_append hprefix tailTrace_6380690
  have hstable : (prefixWord ++ tailWord_6380690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380690).length < 2 ^ (prefixWord ++ tailWord_6380690).sum := by decide
  have hdescent : baseEnd_6380690 < baseStart_6380690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380696 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 1, 8]
def baseStart_6380696 : Nat := 118140960795 + 6380696 * 2 ^ 59
def prefixEnd_6380696 : Nat := 4983230072969 + 3 ^ 40 * 6380696 * 2
def baseEnd_6380696 : Nat := 1092121319406890910418573

theorem tailTrace_6380696 : CollatzResearch.WordTrace tailWord_6380696 prefixEnd_6380696 1092121319406890910418573 := by
  unfold tailWord_6380696
  simp only [CollatzResearch.WordTrace]
  refine ⟨116361551045917801481792971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155148734727890401975723961 116361551045917801481792971)
  ·
    refine ⟨174542326568876702222689457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116361551045917801481792971 174542326568876702222689457)
    ·
      refine ⟨130906744926657526667017093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174542326568876702222689457 130906744926657526667017093)
      ·
        refine ⟨24545014673748286250065705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130906744926657526667017093 24545014673748286250065705)
        ·
          refine ⟨18408761005311214687549279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24545014673748286250065705 18408761005311214687549279)
          ·
            refine ⟨27613141507966822031323919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18408761005311214687549279 27613141507966822031323919)
            ·
              refine ⟨41419712261950233046985879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27613141507966822031323919 41419712261950233046985879)
              ·
                refine ⟨62129568392925349570478819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41419712261950233046985879 62129568392925349570478819)
                ·
                  refine ⟨93194352589388024355718229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62129568392925349570478819 93194352589388024355718229)
                  ·
                    refine ⟨1092121319406890910418573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93194352589388024355718229 1092121319406890910418573)
                    ·
                      rfl

theorem cell23_6380696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_6380696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380696 prefixEnd_6380696 := by exact prefixLift 6380696
  have htrace : WordTrace (prefixWord ++ tailWord_6380696) baseStart_6380696 baseEnd_6380696 := by
    simpa [prefixWord, tailWord_6380696, baseEnd_6380696] using wordTrace_append hprefix tailTrace_6380696
  have hstable : (prefixWord ++ tailWord_6380696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380696).length < 2 ^ (prefixWord ++ tailWord_6380696).sum := by decide
  have hdescent : baseEnd_6380696 < baseStart_6380696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380754 : List Nat := [3, 2, 2, 2, 1, 1, 5, 1, 2, 2, 2]
def baseStart_6380754 : Nat := 118140960795 + 6380754 * 2 ^ 59
def prefixEnd_6380754 : Nat := 4983230072969 + 3 ^ 40 * 6380754 * 2
def baseEnd_6380754 : Nat := 3276393740098633504330453

theorem tailTrace_6380754 : CollatzResearch.WordTrace tailWord_6380754 prefixEnd_6380754 3276393740098633504330453 := by
  unfold tailWord_6380754
  simp only [CollatzResearch.WordTrace]
  refine ⟨58181304381406369717299329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155150145017083652579464877 58181304381406369717299329)
  ·
    refine ⟨43635978286054777287974497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58181304381406369717299329 43635978286054777287974497)
    ·
      refine ⟨32726983714541082965980873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43635978286054777287974497 32726983714541082965980873)
      ·
        refine ⟨24545237785905812224485655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32726983714541082965980873 24545237785905812224485655)
        ·
          refine ⟨36817856678858718336728483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24545237785905812224485655 36817856678858718336728483)
          ·
            refine ⟨55226785018288077505092725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36817856678858718336728483 55226785018288077505092725)
            ·
              refine ⟨5177511095464507266102443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55226785018288077505092725 5177511095464507266102443)
              ·
                refine ⟨7766266643196760899153665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5177511095464507266102443 7766266643196760899153665)
                ·
                  refine ⟨5824699982397570674365249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7766266643196760899153665 5824699982397570674365249)
                  ·
                    refine ⟨4368524986798178005773937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5824699982397570674365249 4368524986798178005773937)
                    ·
                      refine ⟨3276393740098633504330453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4368524986798178005773937 3276393740098633504330453)
                      ·
                        rfl

theorem cell23_6380754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_6380754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380754 prefixEnd_6380754 := by exact prefixLift 6380754
  have htrace : WordTrace (prefixWord ++ tailWord_6380754) baseStart_6380754 baseEnd_6380754 := by
    simpa [prefixWord, tailWord_6380754, baseEnd_6380754] using wordTrace_append hprefix tailTrace_6380754
  have hstable : (prefixWord ++ tailWord_6380754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380754).length < 2 ^ (prefixWord ++ tailWord_6380754).sum := by decide
  have hdescent : baseEnd_6380754 < baseStart_6380754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380793 : List Nat := [1, 2, 1, 3, 1, 1, 5, 2, 2, 1, 4]
def baseStart_6380793 : Nat := 118140960795 + 6380793 * 2 ^ 59
def prefixEnd_6380793 : Nat := 4983230072969 + 3 ^ 40 * 6380793 * 2
def baseEnd_6380793 : Nat := 3276413765844158851742773

theorem tailTrace_6380793 : CollatzResearch.WordTrace tailWord_6380793 prefixEnd_6380793 3276413765844158851742773 := by
  unfold tailWord_6380793
  simp only [CollatzResearch.WordTrace]
  refine ⟨232726639972484188529867033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155151093314989459019911355 232726639972484188529867033)
  ·
    refine ⟨174544979979363141397400275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232726639972484188529867033 174544979979363141397400275)
    ·
      refine ⟨261817469969044712096100413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174544979979363141397400275 261817469969044712096100413)
      ·
        refine ⟨98181551238391767036037655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261817469969044712096100413 98181551238391767036037655)
        ·
          refine ⟨147272326857587650554056483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98181551238391767036037655 147272326857587650554056483)
          ·
            refine ⟨220908490286381475831084725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147272326857587650554056483 220908490286381475831084725)
            ·
              refine ⟨20710170964348263359164193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 220908490286381475831084725 20710170964348263359164193)
              ·
                refine ⟨15532628223261197519373145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20710170964348263359164193 15532628223261197519373145)
                ·
                  refine ⟨11649471167445898139529859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15532628223261197519373145 11649471167445898139529859)
                  ·
                    refine ⟨17474206751168847209294789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11649471167445898139529859 17474206751168847209294789)
                    ·
                      refine ⟨3276413765844158851742773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17474206751168847209294789 3276413765844158851742773)
                      ·
                        rfl

theorem cell23_6380793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_6380793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380793 prefixEnd_6380793 := by exact prefixLift 6380793
  have htrace : WordTrace (prefixWord ++ tailWord_6380793) baseStart_6380793 baseEnd_6380793 := by
    simpa [prefixWord, tailWord_6380793, baseEnd_6380793] using wordTrace_append hprefix tailTrace_6380793
  have hstable : (prefixWord ++ tailWord_6380793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380793).length < 2 ^ (prefixWord ++ tailWord_6380793).sum := by decide
  have hdescent : baseEnd_6380793 < baseStart_6380793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380850 : List Nat := [3, 2, 1, 1, 4, 2, 2, 2, 6]
def baseStart_6380850 : Nat := 118140960795 + 6380850 * 2 ^ 59
def prefixEnd_6380850 : Nat := 4983230072969 + 3 ^ 40 * 6380850 * 2
def baseEnd_6380850 : Nat := 364049226026829458747779

theorem tailTrace_6380850 : CollatzResearch.WordTrace tailWord_6380850 prefixEnd_6380850 364049226026829458747779 := by
  unfold tailWord_6380850
  simp only [CollatzResearch.WordTrace]
  refine ⟨58182179733319421816173001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155152479288851791509794669 58182179733319421816173001)
  ·
    refine ⟨43636634799989566362129751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58182179733319421816173001 43636634799989566362129751)
    ·
      refine ⟨65454952199984349543194627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43636634799989566362129751 65454952199984349543194627)
      ·
        refine ⟨98182428299976524314791941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65454952199984349543194627 98182428299976524314791941)
        ·
          refine ⟨18409205306245598309023489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98182428299976524314791941 18409205306245598309023489)
          ·
            refine ⟨13806903979684198731767617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18409205306245598309023489 13806903979684198731767617)
            ·
              refine ⟨10355177984763149048825713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13806903979684198731767617 10355177984763149048825713)
              ·
                refine ⟨7766383488572361786619285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10355177984763149048825713 7766383488572361786619285)
                ·
                  refine ⟨364049226026829458747779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7766383488572361786619285 364049226026829458747779)
                  ·
                    rfl

theorem cell23_6380850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_6380850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380850 prefixEnd_6380850 := by exact prefixLift 6380850
  have htrace : WordTrace (prefixWord ++ tailWord_6380850) baseStart_6380850 baseEnd_6380850 := by
    simpa [prefixWord, tailWord_6380850, baseEnd_6380850] using wordTrace_append hprefix tailTrace_6380850
  have hstable : (prefixWord ++ tailWord_6380850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380850).length < 2 ^ (prefixWord ++ tailWord_6380850).sum := by decide
  have hdescent : baseEnd_6380850 < baseStart_6380850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380863 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 3, 5]
def baseStart_6380863 : Nat := 118140960795 + 6380863 * 2 ^ 59
def prefixEnd_6380863 : Nat := 4983230072969 + 3 ^ 40 * 6380863 * 2
def baseEnd_6380863 : Nat := 1092149903163324525955817

theorem tailTrace_6380863 : CollatzResearch.WordTrace tailWord_6380863 prefixEnd_6380863 1092149903163324525955817 := by
  unfold tailWord_6380863
  simp only [CollatzResearch.WordTrace]
  refine ⟨232729193082230590484915243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155152795388153726989943495 232729193082230590484915243)
  ·
    refine ⟨349093789623345885727372865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232729193082230590484915243 349093789623345885727372865)
    ·
      refine ⟨261820342217509414295529649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349093789623345885727372865 261820342217509414295529649)
      ·
        refine ⟨196365256663132060721647237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261820342217509414295529649 196365256663132060721647237)
        ·
          refine ⟨36818485624337261385308857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196365256663132060721647237 36818485624337261385308857)
          ·
            refine ⟨27613864218252946038981643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36818485624337261385308857 27613864218252946038981643)
            ·
              refine ⟨41420796327379419058472465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27613864218252946038981643 41420796327379419058472465)
              ·
                refine ⟨31065597245534564293854349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41420796327379419058472465 31065597245534564293854349)
                ·
                  refine ⟨11649598967075461610195381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31065597245534564293854349 11649598967075461610195381)
                  ·
                    refine ⟨1092149903163324525955817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11649598967075461610195381 1092149903163324525955817)
                    ·
                      rfl

theorem cell23_6380863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 5].length) (baseStart_6380863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380863 prefixEnd_6380863 := by exact prefixLift 6380863
  have htrace : WordTrace (prefixWord ++ tailWord_6380863) baseStart_6380863 baseEnd_6380863 := by
    simpa [prefixWord, tailWord_6380863, baseEnd_6380863] using wordTrace_append hprefix tailTrace_6380863
  have hstable : (prefixWord ++ tailWord_6380863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380863).length < 2 ^ (prefixWord ++ tailWord_6380863).sum := by decide
  have hdescent : baseEnd_6380863 < baseStart_6380863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380883 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 4]
def baseStart_6380883 : Nat := 118140960795 + 6380883 * 2 ^ 59
def prefixEnd_6380883 : Nat := 4983230072969 + 3 ^ 40 * 6380883 * 2
def baseEnd_6380883 : Nat := 3276459979103063499617359

theorem tailTrace_6380883 : CollatzResearch.WordTrace tailWord_6380883 prefixEnd_6380883 3276459979103063499617359 := by
  unfold tailWord_6380883
  simp only [CollatzResearch.WordTrace]
  refine ⟨232729922542158133900643303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155153281694772089267095535 232729922542158133900643303)
  ·
    refine ⟨349094883813237200850964955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232729922542158133900643303 349094883813237200850964955)
    ·
      refine ⟨523642325719855801276447433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349094883813237200850964955 523642325719855801276447433)
      ·
        refine ⟨392731744289891850957335575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523642325719855801276447433 392731744289891850957335575)
        ·
          refine ⟨589097616434837776436003363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392731744289891850957335575 589097616434837776436003363)
          ·
            refine ⟨883646424652256664654005045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589097616434837776436003363 883646424652256664654005045)
            ·
              refine ⟨82841852311149062311312973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 883646424652256664654005045 82841852311149062311312973)
              ·
                refine ⟨31065694616680898366742365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82841852311149062311312973 31065694616680898366742365)
                ·
                  refine ⟨11649635481255336887528387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31065694616680898366742365 11649635481255336887528387)
                  ·
                    refine ⟨17474453221883005331292581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11649635481255336887528387 17474453221883005331292581)
                    ·
                      refine ⟨3276459979103063499617359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17474453221883005331292581 3276459979103063499617359)
                      ·
                        rfl

theorem cell23_6380883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 4].length) (baseStart_6380883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380883 prefixEnd_6380883 := by exact prefixLift 6380883
  have htrace : WordTrace (prefixWord ++ tailWord_6380883) baseStart_6380883 baseEnd_6380883 := by
    simpa [prefixWord, tailWord_6380883, baseEnd_6380883] using wordTrace_append hprefix tailTrace_6380883
  have hstable : (prefixWord ++ tailWord_6380883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380883).length < 2 ^ (prefixWord ++ tailWord_6380883).sum := by decide
  have hdescent : baseEnd_6380883 < baseStart_6380883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380887 : List Nat := [1, 1, 3, 2, 3, 2, 3, 1, 2, 3, 2]
def baseStart_6380887 : Nat := 118140960795 + 6380887 * 2 ^ 59
def prefixEnd_6380887 : Nat := 4983230072969 + 3 ^ 40 * 6380887 * 2
def baseEnd_6380887 : Nat := 3276462033025681483967341

theorem tailTrace_6380887 : CollatzResearch.WordTrace tailWord_6380887 prefixEnd_6380887 3276462033025681483967341 := by
  unfold tailWord_6380887
  simp only [CollatzResearch.WordTrace]
  refine ⟨232730068434143642583788915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155153378956095761722525943 232730068434143642583788915)
  ·
    refine ⟨349095102651215463875683373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232730068434143642583788915 349095102651215463875683373)
    ·
      refine ⟨130910663494205798953381265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349095102651215463875683373 130910663494205798953381265)
      ·
        refine ⟨98182997620654349215035949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130910663494205798953381265 98182997620654349215035949)
        ·
          refine ⟨36818624107745380955638481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98182997620654349215035949 36818624107745380955638481)
          ·
            refine ⟨27613968080809035716728861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36818624107745380955638481 27613968080809035716728861)
            ·
              refine ⟨10355238030303388393773323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27613968080809035716728861 10355238030303388393773323)
              ·
                refine ⟨15532857045455082590659985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10355238030303388393773323 15532857045455082590659985)
                ·
                  refine ⟨11649642784091311942994989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15532857045455082590659985 11649642784091311942994989)
                  ·
                    refine ⟨4368616044034241978623121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11649642784091311942994989 4368616044034241978623121)
                    ·
                      refine ⟨3276462033025681483967341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4368616044034241978623121 3276462033025681483967341)
                      ·
                        rfl

theorem cell23_6380887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_6380887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380887 prefixEnd_6380887 := by exact prefixLift 6380887
  have htrace : WordTrace (prefixWord ++ tailWord_6380887) baseStart_6380887 baseEnd_6380887 := by
    simpa [prefixWord, tailWord_6380887, baseEnd_6380887] using wordTrace_append hprefix tailTrace_6380887
  have hstable : (prefixWord ++ tailWord_6380887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380887).length < 2 ^ (prefixWord ++ tailWord_6380887).sum := by decide
  have hdescent : baseEnd_6380887 < baseStart_6380887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380913 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 3, 2, 4]
def baseStart_6380913 : Nat := 118140960795 + 6380913 * 2 ^ 59
def prefixEnd_6380913 : Nat := 4983230072969 + 3 ^ 40 * 6380913 * 2
def baseEnd_6380913 : Nat := 3276475383522698382242221

theorem tailTrace_6380913 : CollatzResearch.WordTrace tailWord_6380913 prefixEnd_6380913 3276475383522698382242221 := by
  unfold tailWord_6380913
  simp only [CollatzResearch.WordTrace]
  refine ⟨232731016732049449024235393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155154011154699632682823595 232731016732049449024235393)
  ·
    refine ⟨174548262549037086768176545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232731016732049449024235393 174548262549037086768176545)
    ·
      refine ⟨130911196911777815076132409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174548262549037086768176545 130911196911777815076132409)
      ·
        refine ⟨98183397683833361307099307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130911196911777815076132409 98183397683833361307099307)
        ·
          refine ⟨147275096525750041960648961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98183397683833361307099307 147275096525750041960648961)
          ·
            refine ⟨110456322394312531470486721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147275096525750041960648961 110456322394312531470486721)
            ·
              refine ⟨82842241795734398602865041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110456322394312531470486721 82842241795734398602865041)
              ·
                refine ⟨62131681346800798952148781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82842241795734398602865041 62131681346800798952148781)
                ·
                  refine ⟨23299380505050299607055793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62131681346800798952148781 23299380505050299607055793)
                  ·
                    refine ⟨17474535378787724705291845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23299380505050299607055793 17474535378787724705291845)
                    ·
                      refine ⟨3276475383522698382242221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17474535378787724705291845 3276475383522698382242221)
                      ·
                        rfl

theorem cell23_6380913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_6380913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380913 prefixEnd_6380913 := by exact prefixLift 6380913
  have htrace : WordTrace (prefixWord ++ tailWord_6380913) baseStart_6380913 baseEnd_6380913 := by
    simpa [prefixWord, tailWord_6380913, baseEnd_6380913] using wordTrace_append hprefix tailTrace_6380913
  have hstable : (prefixWord ++ tailWord_6380913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380913).length < 2 ^ (prefixWord ++ tailWord_6380913).sum := by decide
  have hdescent : baseEnd_6380913 < baseStart_6380913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380963 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 5]
def baseStart_6380963 : Nat := 118140960795 + 6380963 * 2 ^ 59
def prefixEnd_6380963 : Nat := 4983230072969 + 3 ^ 40 * 6380963 * 2
def baseEnd_6380963 : Nat := 3276501057555423186616991

theorem tailTrace_6380963 : CollatzResearch.WordTrace tailWord_6380963 prefixEnd_6380963 3276501057555423186616991 := by
  unfold tailWord_6380963
  simp only [CollatzResearch.WordTrace]
  refine ⟨232732840381868307563555543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155155226921245538375703695 232732840381868307563555543)
  ·
    refine ⟨349099260572802461345333315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232732840381868307563555543 349099260572802461345333315)
    ·
      refine ⟨523648890859203692017999973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349099260572802461345333315 523648890859203692017999973)
      ·
        refine ⟨98184167036100692253374995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 523648890859203692017999973 98184167036100692253374995)
        ·
          refine ⟨147276250554151038380062493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98184167036100692253374995 147276250554151038380062493)
          ·
            refine ⟨55228593957806639392523435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147276250554151038380062493 55228593957806639392523435)
            ·
              refine ⟨82842890936709959088785153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55228593957806639392523435 82842890936709959088785153)
              ·
                refine ⟨62132168202532469316588865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82842890936709959088785153 62132168202532469316588865)
                ·
                  refine ⟨46599126151899351987441649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62132168202532469316588865 46599126151899351987441649)
                  ·
                    refine ⟨34949344613924513990581237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46599126151899351987441649 34949344613924513990581237)
                    ·
                      refine ⟨3276501057555423186616991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34949344613924513990581237 3276501057555423186616991)
                      ·
                        rfl

theorem cell23_6380963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_6380963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380963 prefixEnd_6380963 := by exact prefixLift 6380963
  have htrace : WordTrace (prefixWord ++ tailWord_6380963) baseStart_6380963 baseEnd_6380963 := by
    simpa [prefixWord, tailWord_6380963, baseEnd_6380963] using wordTrace_append hprefix tailTrace_6380963
  have hstable : (prefixWord ++ tailWord_6380963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380963).length < 2 ^ (prefixWord ++ tailWord_6380963).sum := by decide
  have hdescent : baseEnd_6380963 < baseStart_6380963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380967 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_6380967 : Nat := 118140960795 + 6380967 * 2 ^ 59
def prefixEnd_6380967 : Nat := 4983230072969 + 3 ^ 40 * 6380967 * 2
def baseEnd_6380967 : Nat := 3276503111478041170966973

theorem tailTrace_6380967 : CollatzResearch.WordTrace tailWord_6380967 prefixEnd_6380967 3276503111478041170966973 := by
  unfold tailWord_6380967
  simp only [CollatzResearch.WordTrace]
  refine ⟨232732986273853816246701155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155155324182569210831134103 232732986273853816246701155)
  ·
    refine ⟨349099479410780724370051733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232732986273853816246701155 349099479410780724370051733)
    ·
      refine ⟨16364038097380346454846175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 349099479410780724370051733 16364038097380346454846175)
      ·
        refine ⟨24546057146070519682269263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16364038097380346454846175 24546057146070519682269263)
        ·
          refine ⟨36819085719105779523403895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24546057146070519682269263 36819085719105779523403895)
          ·
            refine ⟨55228628578658669285105843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36819085719105779523403895 55228628578658669285105843)
            ·
              refine ⟨82842942867988003927658765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55228628578658669285105843 82842942867988003927658765)
              ·
                refine ⟨31066103575495501472872037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82842942867988003927658765 31066103575495501472872037)
                ·
                  refine ⟨5824894420405406526163507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31066103575495501472872037 5824894420405406526163507)
                  ·
                    refine ⟨8737341630608109789245261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5824894420405406526163507 8737341630608109789245261)
                    ·
                      refine ⟨3276503111478041170966973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8737341630608109789245261 3276503111478041170966973)
                      ·
                        rfl

theorem cell23_6380967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_6380967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380967 prefixEnd_6380967 := by exact prefixLift 6380967
  have htrace : WordTrace (prefixWord ++ tailWord_6380967) baseStart_6380967 baseEnd_6380967 := by
    simpa [prefixWord, tailWord_6380967, baseEnd_6380967] using wordTrace_append hprefix tailTrace_6380967
  have hstable : (prefixWord ++ tailWord_6380967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380967).length < 2 ^ (prefixWord ++ tailWord_6380967).sum := by decide
  have hdescent : baseEnd_6380967 < baseStart_6380967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380968 : List Nat := [2, 1, 6, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_6380968 : Nat := 118140960795 + 6380968 * 2 ^ 59
def prefixEnd_6380968 : Nat := 4983230072969 + 3 ^ 40 * 6380968 * 2
def baseEnd_6380968 : Nat := 3276503624958695667054469

theorem tailTrace_6380968 : CollatzResearch.WordTrace tailWord_6380968 prefixEnd_6380968 3276503624958695667054469 := by
  unfold tailWord_6380968
  simp only [CollatzResearch.WordTrace]
  refine ⟨116366511373425096708743779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155155348497900128944991705 116366511373425096708743779)
  ·
    refine ⟨174549767060137645063115669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116366511373425096708743779 174549767060137645063115669)
    ·
      refine ⟨8182020330943952112333547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 174549767060137645063115669 8182020330943952112333547)
      ·
        refine ⟨12273030496415928168500321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8182020330943952112333547 12273030496415928168500321)
        ·
          refine ⟨9204772872311946126375241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12273030496415928168500321 9204772872311946126375241)
          ·
            refine ⟨6903579654233959594781431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9204772872311946126375241 6903579654233959594781431)
            ·
              refine ⟨10355369481350939392172147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6903579654233959594781431 10355369481350939392172147)
              ·
                refine ⟨15533054222026409088258221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10355369481350939392172147 15533054222026409088258221)
                ·
                  refine ⟨5824895333259903408096833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15533054222026409088258221 5824895333259903408096833)
                  ·
                    refine ⟨4368671499944927556072625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5824895333259903408096833 4368671499944927556072625)
                    ·
                      refine ⟨3276503624958695667054469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4368671499944927556072625 3276503624958695667054469)
                      ·
                        rfl

theorem cell23_6380968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_6380968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380968 prefixEnd_6380968 := by exact prefixLift 6380968
  have htrace : WordTrace (prefixWord ++ tailWord_6380968) baseStart_6380968 baseEnd_6380968 := by
    simpa [prefixWord, tailWord_6380968, baseEnd_6380968] using wordTrace_append hprefix tailTrace_6380968
  have hstable : (prefixWord ++ tailWord_6380968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380968).length < 2 ^ (prefixWord ++ tailWord_6380968).sum := by decide
  have hdescent : baseEnd_6380968 < baseStart_6380968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380977 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 3, 3, 2]
def baseStart_6380977 : Nat := 118140960795 + 6380977 * 2 ^ 59
def prefixEnd_6380977 : Nat := 4983230072969 + 3 ^ 40 * 6380977 * 2
def baseEnd_6380977 : Nat := 3276508246284586131841927

theorem tailTrace_6380977 : CollatzResearch.WordTrace tailWord_6380977 prefixEnd_6380977 3276508246284586131841927 := by
  unfold tailWord_6380977
  simp only [CollatzResearch.WordTrace]
  refine ⟨232733351003817587954565185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155155567335878391969710123 232733351003817587954565185)
  ·
    refine ⟨174550013252863190965923889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232733351003817587954565185 174550013252863190965923889)
    ·
      refine ⟨130912509939647393224442917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174550013252863190965923889 130912509939647393224442917)
      ·
        refine ⟨24546095613683886229583047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130912509939647393224442917 24546095613683886229583047)
        ·
          refine ⟨36819143420525829344374571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24546095613683886229583047 36819143420525829344374571)
          ·
            refine ⟨55228715130788744016561857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36819143420525829344374571 55228715130788744016561857)
            ·
              refine ⟨41421536348091558012421393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55228715130788744016561857 41421536348091558012421393)
              ·
                refine ⟨31066152261068668509316045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41421536348091558012421393 31066152261068668509316045)
                ·
                  refine ⟨11649807097900750690993517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31066152261068668509316045 11649807097900750690993517)
                  ·
                    refine ⟨4368677661712781509122569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11649807097900750690993517 4368677661712781509122569)
                    ·
                      refine ⟨3276508246284586131841927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4368677661712781509122569 3276508246284586131841927)
                      ·
                        rfl

theorem cell23_6380977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_6380977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380977 prefixEnd_6380977 := by exact prefixLift 6380977
  have htrace : WordTrace (prefixWord ++ tailWord_6380977) baseStart_6380977 baseEnd_6380977 := by
    simpa [prefixWord, tailWord_6380977, baseEnd_6380977] using wordTrace_append hprefix tailTrace_6380977
  have hstable : (prefixWord ++ tailWord_6380977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380977).length < 2 ^ (prefixWord ++ tailWord_6380977).sum := by decide
  have hdescent : baseEnd_6380977 < baseStart_6380977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380983 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 1, 8]
def baseStart_6380983 : Nat := 118140960795 + 6380983 * 2 ^ 59
def prefixEnd_6380983 : Nat := 4983230072969 + 3 ^ 40 * 6380983 * 2
def baseEnd_6380983 : Nat := 1092170442389504369455633

theorem tailTrace_6380983 : CollatzResearch.WordTrace tailWord_6380983 prefixEnd_6380983 1092170442389504369455633 := by
  unfold tailWord_6380983
  simp only [CollatzResearch.WordTrace]
  refine ⟨232733569841795850979283603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155155713227863900652855735 232733569841795850979283603)
  ·
    refine ⟨349100354762693776468925405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232733569841795850979283603 349100354762693776468925405)
    ·
      refine ⟨130912633036010166175847027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349100354762693776468925405 130912633036010166175847027)
      ·
        refine ⟨196368949554015249263770541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130912633036010166175847027 196368949554015249263770541)
        ·
          refine ⟨73638356082755718473913953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196368949554015249263770541 73638356082755718473913953)
          ·
            refine ⟨55228767062066788855435465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73638356082755718473913953 55228767062066788855435465)
            ·
              refine ⟨41421575296550091641576599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55228767062066788855435465 41421575296550091641576599)
              ·
                refine ⟨62132362944825137462364899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41421575296550091641576599 62132362944825137462364899)
                ·
                  refine ⟨93198544417237706193547349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62132362944825137462364899 93198544417237706193547349)
                  ·
                    refine ⟨1092170442389504369455633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93198544417237706193547349 1092170442389504369455633)
                    ·
                      rfl

theorem cell23_6380983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_6380983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380983 prefixEnd_6380983 := by exact prefixLift 6380983
  have htrace : WordTrace (prefixWord ++ tailWord_6380983) baseStart_6380983 baseEnd_6380983 := by
    simpa [prefixWord, tailWord_6380983, baseEnd_6380983] using wordTrace_append hprefix tailTrace_6380983
  have hstable : (prefixWord ++ tailWord_6380983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380983).length < 2 ^ (prefixWord ++ tailWord_6380983).sum := by decide
  have hdescent : baseEnd_6380983 < baseStart_6380983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6380984 : List Nat := [2, 1, 2, 1, 2, 2, 6, 1, 2, 1, 3]
def baseStart_6380984 : Nat := 118140960795 + 6380984 * 2 ^ 59
def prefixEnd_6380984 : Nat := 4983230072969 + 3 ^ 40 * 6380984 * 2
def baseEnd_6380984 : Nat := 3276511840649167604454395

theorem tailTrace_6380984 : CollatzResearch.WordTrace tailWord_6380984 prefixEnd_6380984 3276511840649167604454395 := by
  unfold tailWord_6380984
  simp only [CollatzResearch.WordTrace]
  refine ⟨116366803157396114075035003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155155737543194818766713337 116366803157396114075035003)
  ·
    refine ⟨174550204736094171112552505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116366803157396114075035003 174550204736094171112552505)
    ·
      refine ⟨130912653552070628334414379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174550204736094171112552505 130912653552070628334414379)
      ·
        refine ⟨196368980328105942501621569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130912653552070628334414379 196368980328105942501621569)
        ·
          refine ⟨147276735246079456876216177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196368980328105942501621569 147276735246079456876216177)
          ·
            refine ⟨110457551434559592657162133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147276735246079456876216177 110457551434559592657162133)
            ·
              refine ⟨5177697723494980905804475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110457551434559592657162133 5177697723494980905804475)
              ·
                refine ⟨7766546585242471358706713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5177697723494980905804475 7766546585242471358706713)
                ·
                  refine ⟨5824909938931853519030035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7766546585242471358706713 5824909938931853519030035)
                  ·
                    refine ⟨8737364908397780278545053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5824909938931853519030035 8737364908397780278545053)
                    ·
                      refine ⟨3276511840649167604454395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8737364908397780278545053 3276511840649167604454395)
                      ·
                        rfl

theorem cell23_6380984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 2, 1, 3].length) (baseStart_6380984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6380984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6380984 prefixEnd_6380984 := by exact prefixLift 6380984
  have htrace : WordTrace (prefixWord ++ tailWord_6380984) baseStart_6380984 baseEnd_6380984 := by
    simpa [prefixWord, tailWord_6380984, baseEnd_6380984] using wordTrace_append hprefix tailTrace_6380984
  have hstable : (prefixWord ++ tailWord_6380984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6380984).length < 2 ^ (prefixWord ++ tailWord_6380984).sum := by decide
  have hdescent : baseEnd_6380984 < baseStart_6380984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6380984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381007 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 6, 2, 2]
def baseStart_6381007 : Nat := 118140960795 + 6381007 * 2 ^ 59
def prefixEnd_6381007 : Nat := 4983230072969 + 3 ^ 40 * 6381007 * 2
def baseEnd_6381007 : Nat := 3276523650704221014466789

theorem tailTrace_6381007 : CollatzResearch.WordTrace tailWord_6381007 prefixEnd_6381007 3276523650704221014466789 := by
  unfold tailWord_6381007
  simp only [CollatzResearch.WordTrace]
  refine ⟨232734445193708903078157275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155156296795805935385438183 232734445193708903078157275)
  ·
    refine ⟨349101667790563354617235913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232734445193708903078157275 349101667790563354617235913)
    ·
      refine ⟨261826250842922515962926935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349101667790563354617235913 261826250842922515962926935)
      ·
        refine ⟨392739376264383773944390403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261826250842922515962926935 392739376264383773944390403)
        ·
          refine ⟨589109064396575660916585605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392739376264383773944390403 589109064396575660916585605)
          ·
            refine ⟨110457949574357936421859801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 589109064396575660916585605 110457949574357936421859801)
            ·
              refine ⟨82843462180768452316394851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110457949574357936421859801 82843462180768452316394851)
              ·
                refine ⟨124265193271152678474592277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82843462180768452316394851 124265193271152678474592277)
                ·
                  refine ⟨5824930934585281803496513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124265193271152678474592277 5824930934585281803496513)
                  ·
                    refine ⟨4368698200938961352622385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5824930934585281803496513 4368698200938961352622385)
                    ·
                      refine ⟨3276523650704221014466789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4368698200938961352622385 3276523650704221014466789)
                      ·
                        rfl

theorem cell23_6381007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 2, 2].length) (baseStart_6381007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381007 prefixEnd_6381007 := by exact prefixLift 6381007
  have htrace : WordTrace (prefixWord ++ tailWord_6381007) baseStart_6381007 baseEnd_6381007 := by
    simpa [prefixWord, tailWord_6381007, baseEnd_6381007] using wordTrace_append hprefix tailTrace_6381007
  have hstable : (prefixWord ++ tailWord_6381007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381007).length < 2 ^ (prefixWord ++ tailWord_6381007).sum := by decide
  have hdescent : baseEnd_6381007 < baseStart_6381007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381040 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 3]
def baseStart_6381040 : Nat := 118140960795 + 6381040 * 2 ^ 59
def prefixEnd_6381040 : Nat := 4983230072969 + 3 ^ 40 * 6381040 * 2
def baseEnd_6381040 : Nat := 3276540595565819385354137

theorem tailTrace_6381040 : CollatzResearch.WordTrace tailWord_6381040 prefixEnd_6381040 3276540595565819385354137 := by
  unfold tailWord_6381040
  simp only [CollatzResearch.WordTrace]
  refine ⟨116367824401294674857054287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155157099201726233142739049 116367824401294674857054287)
  ·
    refine ⟨174551736601942012285581431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116367824401294674857054287 174551736601942012285581431)
    ·
      refine ⟨261827604902913018428372147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174551736601942012285581431 261827604902913018428372147)
      ·
        refine ⟨392741407354369527642558221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261827604902913018428372147 392741407354369527642558221)
        ·
          refine ⟨147278027757888572865959333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392741407354369527642558221 147278027757888572865959333)
          ·
            refine ⟨27614630204604107412367375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147278027757888572865959333 27614630204604107412367375)
            ·
              refine ⟨41421945306906161118551063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27614630204604107412367375 41421945306906161118551063)
              ·
                refine ⟨62132917960359241677826595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41421945306906161118551063 62132917960359241677826595)
                ·
                  refine ⟨93199376940538862516739893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62132917960359241677826595 93199376940538862516739893)
                  ·
                    refine ⟨8737441588175518360944365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93199376940538862516739893 8737441588175518360944365)
                    ·
                      refine ⟨3276540595565819385354137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8737441588175518360944365 3276540595565819385354137)
                      ·
                        rfl

theorem cell23_6381040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 3].length) (baseStart_6381040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381040 prefixEnd_6381040 := by exact prefixLift 6381040
  have htrace : WordTrace (prefixWord ++ tailWord_6381040) baseStart_6381040 baseEnd_6381040 := by
    simpa [prefixWord, tailWord_6381040, baseEnd_6381040] using wordTrace_append hprefix tailTrace_6381040
  have hstable : (prefixWord ++ tailWord_6381040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381040).length < 2 ^ (prefixWord ++ tailWord_6381040).sum := by decide
  have hdescent : baseEnd_6381040 < baseStart_6381040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381107 : List Nat := [1, 1, 1, 2, 4, 3, 2, 2, 3, 4]
def baseStart_6381107 : Nat := 118140960795 + 6381107 * 2 ^ 59
def prefixEnd_6381107 : Nat := 4983230072969 + 3 ^ 40 * 6381107 * 2
def baseEnd_6381107 : Nat := 1092191666256556874405443

theorem tailTrace_6381107 : CollatzResearch.WordTrace tailWord_6381107 prefixEnd_6381107 1092191666256556874405443 := by
  unfold tailWord_6381107
  simp only [CollatzResearch.WordTrace]
  refine ⟨232738092493346620156797575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155158728328897746771198383 232738092493346620156797575)
  ·
    refine ⟨349107138740019930235196363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232738092493346620156797575 349107138740019930235196363)
    ·
      refine ⟨523660708110029895352794545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349107138740019930235196363 523660708110029895352794545)
      ·
        refine ⟨392745531082522421514595909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523660708110029895352794545 392745531082522421514595909)
        ·
          refine ⟨73639787077972954033986733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 392745531082522421514595909 73639787077972954033986733)
          ·
            refine ⟨27614920154239857762745025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73639787077972954033986733 27614920154239857762745025)
            ·
              refine ⟨20711190115679893322058769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27614920154239857762745025 20711190115679893322058769)
              ·
                refine ⟨15533392586759919991544077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20711190115679893322058769 15533392586759919991544077)
                ·
                  refine ⟨5825022220034969996829029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15533392586759919991544077 5825022220034969996829029)
                  ·
                    refine ⟨1092191666256556874405443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5825022220034969996829029 1092191666256556874405443)
                    ·
                      rfl

theorem cell23_6381107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 4].length) (baseStart_6381107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381107 prefixEnd_6381107 := by exact prefixLift 6381107
  have htrace : WordTrace (prefixWord ++ tailWord_6381107) baseStart_6381107 baseEnd_6381107 := by
    simpa [prefixWord, tailWord_6381107, baseEnd_6381107] using wordTrace_append hprefix tailTrace_6381107
  have hstable : (prefixWord ++ tailWord_6381107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381107).length < 2 ^ (prefixWord ++ tailWord_6381107).sum := by decide
  have hdescent : baseEnd_6381107 < baseStart_6381107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381184 : List Nat := [2, 1, 1, 2, 1, 4, 5, 1, 1, 5]
def baseStart_6381184 : Nat := 118140960795 + 6381184 * 2 ^ 59
def prefixEnd_6381184 : Nat := 4983230072969 + 3 ^ 40 * 6381184 * 2
def baseEnd_6381184 : Nat := 1092204845593355607317825

theorem tailTrace_6381184 : CollatzResearch.WordTrace tailWord_6381184 prefixEnd_6381184 1092204845593355607317825 := by
  unfold tailWord_6381184
  simp only [CollatzResearch.WordTrace]
  refine ⟨116370450457033831153675303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155160600609378441538233737 116370450457033831153675303)
  ·
    refine ⟨174555675685550746730512955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116370450457033831153675303 174555675685550746730512955)
    ·
      refine ⟨261833513528326120095769433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174555675685550746730512955 261833513528326120095769433)
      ·
        refine ⟨196375135146244590071827075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261833513528326120095769433 196375135146244590071827075)
        ·
          refine ⟨294562702719366885107740613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196375135146244590071827075 294562702719366885107740613)
          ·
            refine ⟨55230506759881290957701365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 294562702719366885107740613 55230506759881290957701365)
            ·
              refine ⟨5177860008738871027284503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55230506759881290957701365 5177860008738871027284503)
              ·
                refine ⟨7766790013108306540926755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5177860008738871027284503 7766790013108306540926755)
                ·
                  refine ⟨11650185019662459811390133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7766790013108306540926755 11650185019662459811390133)
                  ·
                    refine ⟨1092204845593355607317825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11650185019662459811390133 1092204845593355607317825)
                    ·
                      rfl

theorem cell23_6381184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 1, 5].length) (baseStart_6381184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381184 prefixEnd_6381184 := by exact prefixLift 6381184
  have htrace : WordTrace (prefixWord ++ tailWord_6381184) baseStart_6381184 baseEnd_6381184 := by
    simpa [prefixWord, tailWord_6381184, baseEnd_6381184] using wordTrace_append hprefix tailTrace_6381184
  have hstable : (prefixWord ++ tailWord_6381184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381184).length < 2 ^ (prefixWord ++ tailWord_6381184).sum := by decide
  have hdescent : baseEnd_6381184 < baseStart_6381184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381192 : List Nat := [2, 1, 3, 5, 2, 1, 2, 2, 1, 4]
def baseStart_6381192 : Nat := 118140960795 + 6381192 * 2 ^ 59
def prefixEnd_6381192 : Nat := 4983230072969 + 3 ^ 40 * 6381192 * 2
def baseEnd_6381192 : Nat := 1092206214875100930217813

theorem tailTrace_6381192 : CollatzResearch.WordTrace tailWord_6381192 prefixEnd_6381192 1092206214875100930217813 := by
  unfold tailWord_6381192
  simp only [CollatzResearch.WordTrace]
  refine ⟨116370596349019339836820915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155160795132025786449094553 116370596349019339836820915)
  ·
    refine ⟨174555894523529009755231373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116370596349019339836820915 174555894523529009755231373)
    ·
      refine ⟨65458460446323378658211765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174555894523529009755231373 65458460446323378658211765)
      ·
        refine ⟨6136730666842816749207353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65458460446323378658211765 6136730666842816749207353)
        ·
          refine ⟨4602548000132112561905515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6136730666842816749207353 4602548000132112561905515)
          ·
            refine ⟨6903822000198168842858273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4602548000132112561905515 6903822000198168842858273)
            ·
              refine ⟨5177866500148626632143705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6903822000198168842858273 5177866500148626632143705)
              ·
                refine ⟨3883399875111469974107779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5177866500148626632143705 3883399875111469974107779)
                ·
                  refine ⟨5825099812667204961161669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3883399875111469974107779 5825099812667204961161669)
                  ·
                    refine ⟨1092206214875100930217813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5825099812667204961161669 1092206214875100930217813)
                    ·
                      rfl

theorem cell23_6381192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_6381192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381192 prefixEnd_6381192 := by exact prefixLift 6381192
  have htrace : WordTrace (prefixWord ++ tailWord_6381192) baseStart_6381192 baseEnd_6381192 := by
    simpa [prefixWord, tailWord_6381192, baseEnd_6381192] using wordTrace_append hprefix tailTrace_6381192
  have hstable : (prefixWord ++ tailWord_6381192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381192).length < 2 ^ (prefixWord ++ tailWord_6381192).sum := by decide
  have hdescent : baseEnd_6381192 < baseStart_6381192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381198 : List Nat := [4, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3]
def baseStart_6381198 : Nat := 118140960795 + 6381198 * 2 ^ 59
def prefixEnd_6381198 : Nat := 4983230072969 + 3 ^ 40 * 6381198 * 2
def baseEnd_6381198 : Nat := 3276621725509229767178411

theorem tailTrace_6381198 : CollatzResearch.WordTrace tailWord_6381198 prefixEnd_6381198 3276621725509229767178411 := by
  unfold tailWord_6381198
  simp only [CollatzResearch.WordTrace]
  refine ⟨29092676442002117837295031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155160941024011295132240165 29092676442002117837295031)
  ·
    refine ⟨43639014663003176755942547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29092676442002117837295031 43639014663003176755942547)
    ·
      refine ⟨65458521994504765133913821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43639014663003176755942547 65458521994504765133913821)
      ·
        refine ⟨24546945747939286925217683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65458521994504765133913821 24546945747939286925217683)
        ·
          refine ⟨36820418621908930387826525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24546945747939286925217683 36820418621908930387826525)
          ·
            refine ⟨13807656983215848895434947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36820418621908930387826525 13807656983215848895434947)
            ·
              refine ⟨20711485474823773343152421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13807656983215848895434947 20711485474823773343152421)
              ·
                refine ⟨3883403526529457501841079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20711485474823773343152421 3883403526529457501841079)
                ·
                  refine ⟨5825105289794186252761619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3883403526529457501841079 5825105289794186252761619)
                  ·
                    refine ⟨8737657934691279379142429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5825105289794186252761619 8737657934691279379142429)
                    ·
                      refine ⟨3276621725509229767178411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8737657934691279379142429 3276621725509229767178411)
                      ·
                        rfl

theorem cell23_6381198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_6381198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381198 prefixEnd_6381198 := by exact prefixLift 6381198
  have htrace : WordTrace (prefixWord ++ tailWord_6381198) baseStart_6381198 baseEnd_6381198 := by
    simpa [prefixWord, tailWord_6381198, baseEnd_6381198] using wordTrace_append hprefix tailTrace_6381198
  have hstable : (prefixWord ++ tailWord_6381198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381198).length < 2 ^ (prefixWord ++ tailWord_6381198).sum := by decide
  have hdescent : baseEnd_6381198 < baseStart_6381198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381200 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 6]
def baseStart_6381200 : Nat := 118140960795 + 6381200 * 2 ^ 59
def prefixEnd_6381200 : Nat := 4983230072969 + 3 ^ 40 * 6381200 * 2
def baseEnd_6381200 : Nat := 3276622752470538759353401

theorem tailTrace_6381200 : CollatzResearch.WordTrace tailWord_6381200 prefixEnd_6381200 3276622752470538759353401 := by
  unfold tailWord_6381200
  simp only [CollatzResearch.WordTrace]
  refine ⟨116370742241004848519966527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155160989654673131359955369 116370742241004848519966527)
  ·
    refine ⟨174556113361507272779949791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116370742241004848519966527 174556113361507272779949791)
    ·
      refine ⟨261834170042260909169924687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174556113361507272779949791 261834170042260909169924687)
      ·
        refine ⟨392751255063391363754887031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261834170042260909169924687 392751255063391363754887031)
        ·
          refine ⟨589126882595087045632330547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392751255063391363754887031 589126882595087045632330547)
          ·
            refine ⟨883690323892630568448495821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589126882595087045632330547 883690323892630568448495821)
            ·
              refine ⟨331383871459736463168185933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 883690323892630568448495821 331383871459736463168185933)
              ·
                refine ⟨124268951797401173688069725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331383871459736463168185933 124268951797401173688069725)
                ·
                  refine ⟨46600856924025440133026147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124268951797401173688069725 46600856924025440133026147)
                  ·
                    refine ⟨69901285386038160199539221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46600856924025440133026147 69901285386038160199539221)
                    ·
                      refine ⟨3276622752470538759353401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69901285386038160199539221 3276622752470538759353401)
                      ·
                        rfl

theorem cell23_6381200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_6381200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381200 prefixEnd_6381200 := by exact prefixLift 6381200
  have htrace : WordTrace (prefixWord ++ tailWord_6381200) baseStart_6381200 baseEnd_6381200 := by
    simpa [prefixWord, tailWord_6381200, baseEnd_6381200] using wordTrace_append hprefix tailTrace_6381200
  have hstable : (prefixWord ++ tailWord_6381200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381200).length < 2 ^ (prefixWord ++ tailWord_6381200).sum := by decide
  have hdescent : baseEnd_6381200 < baseStart_6381200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381214 : List Nat := [4, 3, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_6381214 : Nat := 118140960795 + 6381214 * 2 ^ 59
def prefixEnd_6381214 : Nat := 4983230072969 + 3 ^ 40 * 6381214 * 2
def baseEnd_6381214 : Nat := 1092209980399900568192779

theorem tailTrace_6381214 : CollatzResearch.WordTrace tailWord_6381214 prefixEnd_6381214 1092209980399900568192779 := by
  unfold tailWord_6381214
  simp only [CollatzResearch.WordTrace]
  refine ⟨29092749387994872178867837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155161330069305984953961797 29092749387994872178867837)
  ·
    refine ⟨10909781020498077067075439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29092749387994872178867837 10909781020498077067075439)
    ·
      refine ⟨16364671530747115600613159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10909781020498077067075439 16364671530747115600613159)
      ·
        refine ⟨24547007296120673400919739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16364671530747115600613159 24547007296120673400919739)
        ·
          refine ⟨36820510944181010101379609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24547007296120673400919739 36820510944181010101379609)
          ·
            refine ⟨27615383208135757576034707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36820510944181010101379609 27615383208135757576034707)
            ·
              refine ⟨41423074812203636364052061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27615383208135757576034707 41423074812203636364052061)
              ·
                refine ⟨15533653054576363636519523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41423074812203636364052061 15533653054576363636519523)
                ·
                  refine ⟨23300479581864545454779285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15533653054576363636519523 23300479581864545454779285)
                  ·
                    refine ⟨1092209980399900568192779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23300479581864545454779285 1092209980399900568192779)
                    ·
                      rfl

theorem cell23_6381214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_6381214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381214 prefixEnd_6381214 := by exact prefixLift 6381214
  have htrace : WordTrace (prefixWord ++ tailWord_6381214) baseStart_6381214 baseEnd_6381214 := by
    simpa [prefixWord, tailWord_6381214, baseEnd_6381214] using wordTrace_append hprefix tailTrace_6381214
  have hstable : (prefixWord ++ tailWord_6381214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381214).length < 2 ^ (prefixWord ++ tailWord_6381214).sum := by decide
  have hdescent : baseEnd_6381214 < baseStart_6381214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381238 : List Nat := [5, 1, 3, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_6381238 : Nat := 118140960795 + 6381238 * 2 ^ 59
def prefixEnd_6381238 : Nat := 4983230072969 + 3 ^ 40 * 6381238 * 2
def baseEnd_6381238 : Nat := 3276642264735409610678227

theorem tailTrace_6381238 : CollatzResearch.WordTrace tailWord_6381238 prefixEnd_6381238 3276642264735409610678227 := by
  unfold tailWord_6381238
  simp only [CollatzResearch.WordTrace]
  refine ⟨14546429403492001845613523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155161913637248019686544245 14546429403492001845613523)
  ·
    refine ⟨21819644105238002768420285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14546429403492001845613523 21819644105238002768420285)
    ·
      refine ⟨8182366539464251038157607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21819644105238002768420285 8182366539464251038157607)
      ·
        refine ⟨12273549809196376557236411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8182366539464251038157607 12273549809196376557236411)
        ·
          refine ⟨18410324713794564835854617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12273549809196376557236411 18410324713794564835854617)
          ·
            refine ⟨13807743535345923626890963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18410324713794564835854617 13807743535345923626890963)
            ·
              refine ⟨20711615303018885440336445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13807743535345923626890963 20711615303018885440336445)
              ·
                refine ⟨7766855738632082040126167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20711615303018885440336445 7766855738632082040126167)
                ·
                  refine ⟨11650283607948123060189251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7766855738632082040126167 11650283607948123060189251)
                  ·
                    refine ⟨17475425411922184590283877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11650283607948123060189251 17475425411922184590283877)
                    ·
                      refine ⟨3276642264735409610678227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17475425411922184590283877 3276642264735409610678227)
                      ·
                        rfl

theorem cell23_6381238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_6381238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381238 prefixEnd_6381238 := by exact prefixLift 6381238
  have htrace : WordTrace (prefixWord ++ tailWord_6381238) baseStart_6381238 baseEnd_6381238 := by
    simpa [prefixWord, tailWord_6381238, baseEnd_6381238] using wordTrace_append hprefix tailTrace_6381238
  have hstable : (prefixWord ++ tailWord_6381238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381238).length < 2 ^ (prefixWord ++ tailWord_6381238).sum := by decide
  have hdescent : baseEnd_6381238 < baseStart_6381238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381241 : List Nat := [1, 2, 1, 4, 1, 1, 6, 1, 1, 2, 3]
def baseStart_6381241 : Nat := 118140960795 + 6381241 * 2 ^ 59
def prefixEnd_6381241 : Nat := 4983230072969 + 3 ^ 40 * 6381241 * 2
def baseEnd_6381241 : Nat := 3276643805177373098940713

theorem tailTrace_6381241 : CollatzResearch.WordTrace tailWord_6381241 prefixEnd_6381241 3276643805177373098940713 := by
  unfold tailWord_6381241
  simp only [CollatzResearch.WordTrace]
  refine ⟨232742979874861161042175577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155161986583240774028117051 232742979874861161042175577)
  ·
    refine ⟨174557234906145870781631683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232742979874861161042175577 174557234906145870781631683)
    ·
      refine ⟨261835852359218806172447525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174557234906145870781631683 261835852359218806172447525)
      ·
        refine ⟨49094222317353526157333911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261835852359218806172447525 49094222317353526157333911)
        ·
          refine ⟨73641333476030289236000867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49094222317353526157333911 73641333476030289236000867)
          ·
            refine ⟨110462000214045433854001301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73641333476030289236000867 110462000214045433854001301)
            ·
              refine ⟨5177906260033379711906311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110462000214045433854001301 5177906260033379711906311)
              ·
                refine ⟨7766859390050069567859467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5177906260033379711906311 7766859390050069567859467)
                ·
                  refine ⟨11650289085075104351789201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7766859390050069567859467 11650289085075104351789201)
                  ·
                    refine ⟨8737716813806328263841901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11650289085075104351789201 8737716813806328263841901)
                    ·
                      refine ⟨3276643805177373098940713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8737716813806328263841901 3276643805177373098940713)
                      ·
                        rfl

theorem cell23_6381241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_6381241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381241 prefixEnd_6381241 := by exact prefixLift 6381241
  have htrace : WordTrace (prefixWord ++ tailWord_6381241) baseStart_6381241 baseEnd_6381241 := by
    simpa [prefixWord, tailWord_6381241, baseEnd_6381241] using wordTrace_append hprefix tailTrace_6381241
  have hstable : (prefixWord ++ tailWord_6381241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381241).length < 2 ^ (prefixWord ++ tailWord_6381241).sum := by decide
  have hdescent : baseEnd_6381241 < baseStart_6381241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381264 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 3, 3, 2]
def baseStart_6381264 : Nat := 118140960795 + 6381264 * 2 ^ 59
def prefixEnd_6381264 : Nat := 4983230072969 + 3 ^ 40 * 6381264 * 2
def baseEnd_6381264 : Nat := 3276655615232426508953107

theorem tailTrace_6381264 : CollatzResearch.WordTrace tailWord_6381264 prefixEnd_6381264 3276655615232426508953107 := by
  unfold tailWord_6381264
  simp only [CollatzResearch.WordTrace]
  refine ⟨116371909376888917985131423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155162545835851890646841897 116371909376888917985131423)
  ·
    refine ⟨174557864065333376977697135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116371909376888917985131423 174557864065333376977697135)
    ·
      refine ⟨261836796098000065466545703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174557864065333376977697135 261836796098000065466545703)
      ·
        refine ⟨392755194147000098199818555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261836796098000065466545703 392755194147000098199818555)
        ·
          refine ⟨589132791220500147299727833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392755194147000098199818555 589132791220500147299727833)
          ·
            refine ⟨441849593415375110474795875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 589132791220500147299727833 441849593415375110474795875)
            ·
              refine ⟨662774390123062665712193813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441849593415375110474795875 662774390123062665712193813)
              ·
                refine ⟨31067549537018562455259085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 662774390123062665712193813 31067549537018562455259085)
                ·
                  refine ⟨11650331076381960920722157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31067549537018562455259085 11650331076381960920722157)
                  ·
                    refine ⟨4368874153643235345270809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11650331076381960920722157 4368874153643235345270809)
                    ·
                      refine ⟨3276655615232426508953107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4368874153643235345270809 3276655615232426508953107)
                      ·
                        rfl

theorem cell23_6381264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 3, 3, 2].length) (baseStart_6381264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381264 prefixEnd_6381264 := by exact prefixLift 6381264
  have htrace : WordTrace (prefixWord ++ tailWord_6381264) baseStart_6381264 baseEnd_6381264 := by
    simpa [prefixWord, tailWord_6381264, baseEnd_6381264] using wordTrace_append hprefix tailTrace_6381264
  have hstable : (prefixWord ++ tailWord_6381264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381264).length < 2 ^ (prefixWord ++ tailWord_6381264).sum := by decide
  have hdescent : baseEnd_6381264 < baseStart_6381264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381297 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 1, 3, 5]
def baseStart_6381297 : Nat := 118140960795 + 6381297 * 2 ^ 59
def prefixEnd_6381297 : Nat := 4983230072969 + 3 ^ 40 * 6381297 * 2
def baseEnd_6381297 : Nat := 3276672560094024879840455

theorem tailTrace_6381297 : CollatzResearch.WordTrace tailWord_6381297 prefixEnd_6381297 3276672560094024879840455 := by
  unfold tailWord_6381297
  simp only [CollatzResearch.WordTrace]
  refine ⟨232745022362658282606214145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155163348241772188404142763 232745022362658282606214145)
  ·
    refine ⟨174558766771993711954660609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232745022362658282606214145 174558766771993711954660609)
    ·
      refine ⟨130919075078995283965995457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174558766771993711954660609 130919075078995283965995457)
      ·
        refine ⟨98189306309246462974496593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130919075078995283965995457 98189306309246462974496593)
        ·
          refine ⟨73641979731934847230872445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98189306309246462974496593 73641979731934847230872445)
          ·
            refine ⟨27615742399475567711577167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73641979731934847230872445 27615742399475567711577167)
            ·
              refine ⟨41423613599213351567365751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27615742399475567711577167 41423613599213351567365751)
              ·
                refine ⟨62135420398820027351048627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41423613599213351567365751 62135420398820027351048627)
                ·
                  refine ⟨93203130598230041026572941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62135420398820027351048627 93203130598230041026572941)
                  ·
                    refine ⟨34951173974336265384964853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93203130598230041026572941 34951173974336265384964853)
                    ·
                      refine ⟨3276672560094024879840455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34951173974336265384964853 3276672560094024879840455)
                      ·
                        rfl

theorem cell23_6381297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_6381297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381297 prefixEnd_6381297 := by exact prefixLift 6381297
  have htrace : WordTrace (prefixWord ++ tailWord_6381297) baseStart_6381297 baseEnd_6381297 := by
    simpa [prefixWord, tailWord_6381297, baseEnd_6381297] using wordTrace_append hprefix tailTrace_6381297
  have hstable : (prefixWord ++ tailWord_6381297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381297).length < 2 ^ (prefixWord ++ tailWord_6381297).sum := by decide
  have hdescent : baseEnd_6381297 < baseStart_6381297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381307 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 4]
def baseStart_6381307 : Nat := 118140960795 + 6381307 * 2 ^ 59
def prefixEnd_6381307 : Nat := 4983230072969 + 3 ^ 40 * 6381307 * 2
def baseEnd_6381307 : Nat := 3276677694900569840715409

theorem tailTrace_6381307 : CollatzResearch.WordTrace tailWord_6381307 prefixEnd_6381307 3276677694900569840715409 := by
  unfold tailWord_6381307
  simp only [CollatzResearch.WordTrace]
  refine ⟨232745387092622054314078175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155163591395081369542718783 232745387092622054314078175)
  ·
    refine ⟨349118080638933081471117263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232745387092622054314078175 349118080638933081471117263)
    ·
      refine ⟨523677120958399622206675895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349118080638933081471117263 523677120958399622206675895)
      ·
        refine ⟨785515681437599433310013843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523677120958399622206675895 785515681437599433310013843)
        ·
          refine ⟨1178273522156399149965020765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785515681437599433310013843 1178273522156399149965020765)
          ·
            refine ⟨441852570808649681236882787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1178273522156399149965020765 441852570808649681236882787)
            ·
              refine ⟨662778856212974521855324181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441852570808649681236882787 662778856212974521855324181)
              ·
                refine ⟨31067758884983180711968321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 662778856212974521855324181 31067758884983180711968321)
                ·
                  refine ⟨23300819163737385533976241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31067758884983180711968321 23300819163737385533976241)
                  ·
                    refine ⟨17475614372803039150482181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23300819163737385533976241 17475614372803039150482181)
                    ·
                      refine ⟨3276677694900569840715409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17475614372803039150482181 3276677694900569840715409)
                      ·
                        rfl

theorem cell23_6381307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 4].length) (baseStart_6381307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381307 prefixEnd_6381307 := by exact prefixLift 6381307
  have htrace : WordTrace (prefixWord ++ tailWord_6381307) baseStart_6381307 baseEnd_6381307 := by
    simpa [prefixWord, tailWord_6381307, baseEnd_6381307] using wordTrace_append hprefix tailTrace_6381307
  have hstable : (prefixWord ++ tailWord_6381307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381307).length < 2 ^ (prefixWord ++ tailWord_6381307).sum := by decide
  have hdescent : baseEnd_6381307 < baseStart_6381307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381311 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 4, 2, 2]
def baseStart_6381311 : Nat := 118140960795 + 6381311 * 2 ^ 59
def prefixEnd_6381311 : Nat := 4983230072969 + 3 ^ 40 * 6381311 * 2
def baseEnd_6381311 : Nat := 3276679748823187825065391

theorem tailTrace_6381311 : CollatzResearch.WordTrace tailWord_6381311 prefixEnd_6381311 3276679748823187825065391 := by
  unfold tailWord_6381311
  simp only [CollatzResearch.WordTrace]
  refine ⟨232745532984607562997223787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155163688656405041998149191 232745532984607562997223787)
  ·
    refine ⟨349118299476911344495835681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232745532984607562997223787 349118299476911344495835681)
    ·
      refine ⟨261838724607683508371876761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349118299476911344495835681 261838724607683508371876761)
      ·
        refine ⟨196379043455762631278907571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261838724607683508371876761 196379043455762631278907571)
        ·
          refine ⟨294568565183643946918361357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196379043455762631278907571 294568565183643946918361357)
          ·
            refine ⟨110463211943866480094385509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294568565183643946918361357 110463211943866480094385509)
            ·
              refine ⟨20711852239474965017697283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110463211943866480094385509 20711852239474965017697283)
              ·
                refine ⟨31067778359212447526545925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20711852239474965017697283 31067778359212447526545925)
                ·
                  refine ⟨5825208442352333911227361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31067778359212447526545925 5825208442352333911227361)
                  ·
                    refine ⟨4368906331764250433420521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5825208442352333911227361 4368906331764250433420521)
                    ·
                      refine ⟨3276679748823187825065391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4368906331764250433420521 3276679748823187825065391)
                      ·
                        rfl

theorem cell23_6381311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 2, 2].length) (baseStart_6381311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381311 prefixEnd_6381311 := by exact prefixLift 6381311
  have htrace : WordTrace (prefixWord ++ tailWord_6381311) baseStart_6381311 baseEnd_6381311 := by
    simpa [prefixWord, tailWord_6381311, baseEnd_6381311] using wordTrace_append hprefix tailTrace_6381311
  have hstable : (prefixWord ++ tailWord_6381311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381311).length < 2 ^ (prefixWord ++ tailWord_6381311).sum := by decide
  have hdescent : baseEnd_6381311 < baseStart_6381311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381314 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_6381314 : Nat := 118140960795 + 6381314 * 2 ^ 59
def prefixEnd_6381314 : Nat := 4983230072969 + 3 ^ 40 * 6381314 * 2
def baseEnd_6381314 : Nat := 3276681289265151313327877

theorem tailTrace_6381314 : CollatzResearch.WordTrace tailWord_6381314 prefixEnd_6381314 3276681289265151313327877 := by
  unfold tailWord_6381314
  simp only [CollatzResearch.WordTrace]
  refine ⟨58186410600899173627395749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155163761602397796339721997 58186410600899173627395749)
  ·
    refine ⟨10909951987668595055136703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58186410600899173627395749 10909951987668595055136703)
    ·
      refine ⟨16364927981502892582705055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10909951987668595055136703 16364927981502892582705055)
      ·
        refine ⟨24547391972254338874057583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16364927981502892582705055 24547391972254338874057583)
        ·
          refine ⟨36821087958381508311086375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24547391972254338874057583 36821087958381508311086375)
          ·
            refine ⟨55231631937572262466629563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36821087958381508311086375 55231631937572262466629563)
            ·
              refine ⟨82847447906358393699944345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55231631937572262466629563 82847447906358393699944345)
              ·
                refine ⟨62135585929768795274958259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82847447906358393699944345 62135585929768795274958259)
                ·
                  refine ⟨93203378894653192912437389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62135585929768795274958259 93203378894653192912437389)
                  ·
                    refine ⟨34951267085494947342164021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93203378894653192912437389 34951267085494947342164021)
                    ·
                      refine ⟨3276681289265151313327877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34951267085494947342164021 3276681289265151313327877)
                      ·
                        rfl

theorem cell23_6381314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_6381314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381314 prefixEnd_6381314 := by exact prefixLift 6381314
  have htrace : WordTrace (prefixWord ++ tailWord_6381314) baseStart_6381314 baseEnd_6381314 := by
    simpa [prefixWord, tailWord_6381314, baseEnd_6381314] using wordTrace_append hprefix tailTrace_6381314
  have hstable : (prefixWord ++ tailWord_6381314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381314).length < 2 ^ (prefixWord ++ tailWord_6381314).sum := by decide
  have hdescent : baseEnd_6381314 < baseStart_6381314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381332 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_6381332 : Nat := 118140960795 + 6381332 * 2 ^ 59
def prefixEnd_6381332 : Nat := 4983230072969 + 3 ^ 40 * 6381332 * 2
def baseEnd_6381332 : Nat := 3276690531916932242902795

theorem tailTrace_6381332 : CollatzResearch.WordTrace tailWord_6381332 prefixEnd_6381332 3276690531916932242902795 := by
  unfold tailWord_6381332
  simp only [CollatzResearch.WordTrace]
  refine ⟨116373149458765741791869125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155164199278354322389158833 116373149458765741791869125)
  ·
    refine ⟨21819965523518576585975461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116373149458765741791869125 21819965523518576585975461)
    ·
      refine ⟨4091243535659733109870399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21819965523518576585975461 4091243535659733109870399)
      ·
        refine ⟨6136865303489599664805599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4091243535659733109870399 6136865303489599664805599)
        ·
          refine ⟨9205297955234399497208399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6136865303489599664805599 9205297955234399497208399)
          ·
            refine ⟨13807946932851599245812599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9205297955234399497208399 13807946932851599245812599)
            ·
              refine ⟨20711920399277398868718899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13807946932851599245812599 20711920399277398868718899)
              ·
                refine ⟨31067880598916098303078349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20711920399277398868718899 31067880598916098303078349)
                ·
                  refine ⟨11650455224593536863654381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31067880598916098303078349 11650455224593536863654381)
                  ·
                    refine ⟨4368920709222576323870393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11650455224593536863654381 4368920709222576323870393)
                    ·
                      refine ⟨3276690531916932242902795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4368920709222576323870393 3276690531916932242902795)
                      ·
                        rfl

theorem cell23_6381332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_6381332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381332 prefixEnd_6381332 := by exact prefixLift 6381332
  have htrace : WordTrace (prefixWord ++ tailWord_6381332) baseStart_6381332 baseEnd_6381332 := by
    simpa [prefixWord, tailWord_6381332, baseEnd_6381332] using wordTrace_append hprefix tailTrace_6381332
  have hstable : (prefixWord ++ tailWord_6381332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381332).length < 2 ^ (prefixWord ++ tailWord_6381332).sum := by decide
  have hdescent : baseEnd_6381332 < baseStart_6381332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381347 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 1, 7]
def baseStart_6381347 : Nat := 118140960795 + 6381347 * 2 ^ 59
def prefixEnd_6381347 : Nat := 4983230072969 + 3 ^ 40 * 6381347 * 2
def baseEnd_6381347 : Nat := 1092232744708916561405075

theorem tailTrace_6381347 : CollatzResearch.WordTrace tailWord_6381347 prefixEnd_6381347 1092232744708916561405075 := by
  unfold tailWord_6381347
  simp only [CollatzResearch.WordTrace]
  refine ⟨232746846012477141145534295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155164564008318094097022863 232746846012477141145534295)
  ·
    refine ⟨349120269018715711718301443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232746846012477141145534295 349120269018715711718301443)
    ·
      refine ⟨523680403528073567577452165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349120269018715711718301443 523680403528073567577452165)
      ·
        refine ⟨98190075661513793920772281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 523680403528073567577452165 98190075661513793920772281)
        ·
          refine ⟨73642556746135345440579211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98190075661513793920772281 73642556746135345440579211)
          ·
            refine ⟨110463835119203018160868817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73642556746135345440579211 110463835119203018160868817)
            ·
              refine ⟨82847876339402263620651613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110463835119203018160868817 82847876339402263620651613)
              ·
                refine ⟨31067953627275848857744355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82847876339402263620651613 31067953627275848857744355)
                ·
                  refine ⟨46601930440913773286616533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31067953627275848857744355 46601930440913773286616533)
                  ·
                    refine ⟨1092232744708916561405075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46601930440913773286616533 1092232744708916561405075)
                    ·
                      rfl

theorem cell23_6381347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 7].length) (baseStart_6381347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381347 prefixEnd_6381347 := by exact prefixLift 6381347
  have htrace : WordTrace (prefixWord ++ tailWord_6381347) baseStart_6381347 baseEnd_6381347 := by
    simpa [prefixWord, tailWord_6381347, baseEnd_6381347] using wordTrace_append hprefix tailTrace_6381347
  have hstable : (prefixWord ++ tailWord_6381347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381347).length < 2 ^ (prefixWord ++ tailWord_6381347).sum := by decide
  have hdescent : baseEnd_6381347 < baseStart_6381347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381368 : List Nat := [2, 1, 2, 1, 3, 5, 2, 2, 5]
def baseStart_6381368 : Nat := 118140960795 + 6381368 * 2 ^ 59
def prefixEnd_6381368 : Nat := 4983230072969 + 3 ^ 40 * 6381368 * 2
def baseEnd_6381368 : Nat := 364078779691166011339181

theorem tailTrace_6381368 : CollatzResearch.WordTrace tailWord_6381368 prefixEnd_6381368 364078779691166011339181 := by
  unfold tailWord_6381368
  simp only [CollatzResearch.WordTrace]
  refine ⟨116373805972700530866024379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155165074630267374488032505 116373805972700530866024379)
  ·
    refine ⟨174560708959050796299036569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116373805972700530866024379 174560708959050796299036569)
    ·
      refine ⟨130920531719288097224277427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174560708959050796299036569 130920531719288097224277427)
      ·
        refine ⟨196380797578932145836416141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130920531719288097224277427 196380797578932145836416141)
        ·
          refine ⟨73642799092099554688656053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196380797578932145836416141 73642799092099554688656053)
          ·
            refine ⟨6904012414884333252061505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73642799092099554688656053 6904012414884333252061505)
            ·
              refine ⟨5178009311163249939046129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6904012414884333252061505 5178009311163249939046129)
              ·
                refine ⟨3883506983372437454284597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5178009311163249939046129 3883506983372437454284597)
                ·
                  refine ⟨364078779691166011339181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3883506983372437454284597 364078779691166011339181)
                  ·
                    rfl

theorem cell23_6381368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 5].length) (baseStart_6381368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381368 prefixEnd_6381368 := by exact prefixLift 6381368
  have htrace : WordTrace (prefixWord ++ tailWord_6381368) baseStart_6381368 baseEnd_6381368 := by
    simpa [prefixWord, tailWord_6381368, baseEnd_6381368] using wordTrace_append hprefix tailTrace_6381368
  have hstable : (prefixWord ++ tailWord_6381368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381368).length < 2 ^ (prefixWord ++ tailWord_6381368).sum := by decide
  have hdescent : baseEnd_6381368 < baseStart_6381368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381421 : List Nat := [1, 5, 1, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_6381421 : Nat := 118140960795 + 6381421 * 2 ^ 59
def prefixEnd_6381421 : Nat := 4983230072969 + 3 ^ 40 * 6381421 * 2
def baseEnd_6381421 : Nat := 3276736231695182394689885

theorem tailTrace_6381421 : CollatzResearch.WordTrace tailWord_6381421 prefixEnd_6381421 3276736231695182394689885 := by
  unfold tailWord_6381421
  simp only [CollatzResearch.WordTrace]
  refine ⟨232749545014209051783728117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155166363342806034522485411 232749545014209051783728117)
  ·
    refine ⟨21820269845082098604724511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232749545014209051783728117 21820269845082098604724511)
    ·
      refine ⟨32730404767623147907086767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21820269845082098604724511 32730404767623147907086767)
      ·
        refine ⟨49095607151434721860630151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32730404767623147907086767 49095607151434721860630151)
        ·
          refine ⟨73643410727152082790945227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49095607151434721860630151 73643410727152082790945227)
          ·
            refine ⟨110465116090728124186417841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73643410727152082790945227 110465116090728124186417841)
            ·
              refine ⟨82848837068046093139813381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110465116090728124186417841 82848837068046093139813381)
              ·
                refine ⟨15534156950258642463715009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82848837068046093139813381 15534156950258642463715009)
                ·
                  refine ⟨11650617712693981847786257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15534156950258642463715009 11650617712693981847786257)
                  ·
                    refine ⟨8737963284520486385839693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11650617712693981847786257 8737963284520486385839693)
                    ·
                      refine ⟨3276736231695182394689885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8737963284520486385839693 3276736231695182394689885)
                      ·
                        rfl

theorem cell23_6381421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_6381421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381421 prefixEnd_6381421 := by exact prefixLift 6381421
  have htrace : WordTrace (prefixWord ++ tailWord_6381421) baseStart_6381421 baseEnd_6381421 := by
    simpa [prefixWord, tailWord_6381421, baseEnd_6381421] using wordTrace_append hprefix tailTrace_6381421
  have hstable : (prefixWord ++ tailWord_6381421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381421).length < 2 ^ (prefixWord ++ tailWord_6381421).sum := by decide
  have hdescent : baseEnd_6381421 < baseStart_6381421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381438 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_6381438 : Nat := 118140960795 + 6381438 * 2 ^ 59
def prefixEnd_6381438 : Nat := 4983230072969 + 3 ^ 40 * 6381438 * 2
def baseEnd_6381438 : Nat := 3276744960866308828177307

theorem tailTrace_6381438 : CollatzResearch.WordTrace tailWord_6381438 prefixEnd_6381438 3276744960866308828177307 := by
  unfold tailWord_6381438
  simp only [CollatzResearch.WordTrace]
  refine ⟨29093770631893432960887121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155166776703431642458064645 29093770631893432960887121)
  ·
    refine ⟨21820327973920074720665341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29093770631893432960887121 21820327973920074720665341)
    ·
      refine ⟨8182622990220028020249503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21820327973920074720665341 8182622990220028020249503)
      ·
        refine ⟨12273934485330042030374255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8182622990220028020249503 12273934485330042030374255)
        ·
          refine ⟨18410901727995063045561383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12273934485330042030374255 18410901727995063045561383)
          ·
            refine ⟨27616352591992594568342075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18410901727995063045561383 27616352591992594568342075)
            ·
              refine ⟨41424528887988891852513113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27616352591992594568342075 41424528887988891852513113)
              ·
                refine ⟨31068396665991668889384835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41424528887988891852513113 31068396665991668889384835)
                ·
                  refine ⟨46602594998987503334077253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31068396665991668889384835 46602594998987503334077253)
                  ·
                    refine ⟨8737986562310156875139485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46602594998987503334077253 8737986562310156875139485)
                    ·
                      refine ⟨3276744960866308828177307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8737986562310156875139485 3276744960866308828177307)
                      ·
                        rfl

theorem cell23_6381438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_6381438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381438 prefixEnd_6381438 := by exact prefixLift 6381438
  have htrace : WordTrace (prefixWord ++ tailWord_6381438) baseStart_6381438 baseEnd_6381438 := by
    simpa [prefixWord, tailWord_6381438, baseEnd_6381438] using wordTrace_append hprefix tailTrace_6381438
  have hstable : (prefixWord ++ tailWord_6381438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381438).length < 2 ^ (prefixWord ++ tailWord_6381438).sum := by decide
  have hdescent : baseEnd_6381438 < baseStart_6381438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381461 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 1, 5, 2]
def baseStart_6381461 : Nat := 118140960795 + 6381461 * 2 ^ 59
def prefixEnd_6381461 : Nat := 4983230072969 + 3 ^ 40 * 6381461 * 2
def baseEnd_6381461 : Nat := 3276756770921362238189701

theorem tailTrace_6381461 : CollatzResearch.WordTrace tailWord_6381461 prefixEnd_6381461 3276756770921362238189701 := by
  unfold tailWord_6381461
  simp only [CollatzResearch.WordTrace]
  refine ⟨232751003934064138615184237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155167335956042759076789491 232751003934064138615184237)
  ·
    refine ⟨87281626475274051980694089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232751003934064138615184237 87281626475274051980694089)
    ·
      refine ⟨65461219856455538985520567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87281626475274051980694089 65461219856455538985520567)
      ·
        refine ⟨98191829784683308478280851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65461219856455538985520567 98191829784683308478280851)
        ·
          refine ⟨147287744677024962717421277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98191829784683308478280851 147287744677024962717421277)
          ·
            refine ⟨55232904253884361019032979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147287744677024962717421277 55232904253884361019032979)
            ·
              refine ⟨82849356380826541528549469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55232904253884361019032979 82849356380826541528549469)
              ·
                refine ⟨31068508642809953073206051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82849356380826541528549469 31068508642809953073206051)
                ·
                  refine ⟨46602762964214929609809077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31068508642809953073206051 46602762964214929609809077)
                  ·
                    refine ⟨4369009027895149650919601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46602762964214929609809077 4369009027895149650919601)
                    ·
                      refine ⟨3276756770921362238189701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4369009027895149650919601 3276756770921362238189701)
                      ·
                        rfl

theorem cell23_6381461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_6381461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381461 prefixEnd_6381461 := by exact prefixLift 6381461
  have htrace : WordTrace (prefixWord ++ tailWord_6381461) baseStart_6381461 baseEnd_6381461 := by
    simpa [prefixWord, tailWord_6381461, baseEnd_6381461] using wordTrace_append hprefix tailTrace_6381461
  have hstable : (prefixWord ++ tailWord_6381461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381461).length < 2 ^ (prefixWord ++ tailWord_6381461).sum := by decide
  have hdescent : baseEnd_6381461 < baseStart_6381461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381492 : List Nat := [2, 5, 2, 1, 2, 2, 2, 1, 6]
def baseStart_6381492 : Nat := 118140960795 + 6381492 * 2 ^ 59
def prefixEnd_6381492 : Nat := 4983230072969 + 3 ^ 40 * 6381492 * 2
def baseEnd_6381492 : Nat := 364085854313516846322451

theorem tailTrace_6381492 : CollatzResearch.WordTrace tailWord_6381492 prefixEnd_6381492 364085854313516846322451 := by
  unfold tailWord_6381492
  simp only [CollatzResearch.WordTrace]
  refine ⟨116376067298475915454781365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155168089731301220606375153 116376067298475915454781365)
  ·
    refine ⟨10910256309232117073885753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116376067298475915454781365 10910256309232117073885753)
    ·
      refine ⟨8182692231924087805414315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10910256309232117073885753 8182692231924087805414315)
      ·
        refine ⟨12274038347886131708121473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8182692231924087805414315 12274038347886131708121473)
        ·
          refine ⟨9205528760914598781091105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12274038347886131708121473 9205528760914598781091105)
          ·
            refine ⟨6904146570685949085818329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9205528760914598781091105 6904146570685949085818329)
            ·
              refine ⟨5178109928014461814363747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6904146570685949085818329 5178109928014461814363747)
              ·
                refine ⟨7767164892021692721545621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5178109928014461814363747 7767164892021692721545621)
                ·
                  refine ⟨364085854313516846322451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7767164892021692721545621 364085854313516846322451)
                  ·
                    rfl

theorem cell23_6381492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_6381492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381492 prefixEnd_6381492 := by exact prefixLift 6381492
  have htrace : WordTrace (prefixWord ++ tailWord_6381492) baseStart_6381492 baseEnd_6381492 := by
    simpa [prefixWord, tailWord_6381492, baseEnd_6381492] using wordTrace_append hprefix tailTrace_6381492
  have hstable : (prefixWord ++ tailWord_6381492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381492).length < 2 ^ (prefixWord ++ tailWord_6381492).sum := by decide
  have hdescent : baseEnd_6381492 < baseStart_6381492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381504 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 6]
def baseStart_6381504 : Nat := 118140960795 + 6381504 * 2 ^ 59
def prefixEnd_6381504 : Nat := 4983230072969 + 3 ^ 40 * 6381504 * 2
def baseEnd_6381504 : Nat := 3276778850589505569952003

theorem tailTrace_6381504 : CollatzResearch.WordTrace tailWord_6381504 prefixEnd_6381504 3276778850589505569952003 := by
  unfold tailWord_6381504
  simp only [CollatzResearch.WordTrace]
  refine ⟨116376286136454178479499783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155168381515272237972666377 116376286136454178479499783)
  ·
    refine ⟨174564429204681267719249675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116376286136454178479499783 174564429204681267719249675)
    ·
      refine ⟨261846643807021901578874513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174564429204681267719249675 261846643807021901578874513)
      ·
        refine ⟨196384982855266426184155885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261846643807021901578874513 196384982855266426184155885)
        ·
          refine ⟨73644368570724909819058457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196384982855266426184155885 73644368570724909819058457)
          ·
            refine ⟨55233276428043682364293843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73644368570724909819058457 55233276428043682364293843)
            ·
              refine ⟨82849914642065523546440765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55233276428043682364293843 82849914642065523546440765)
              ·
                refine ⟨31068717990774571329915287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82849914642065523546440765 31068717990774571329915287)
                ·
                  refine ⟨46603076986161856994872931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31068717990774571329915287 46603076986161856994872931)
                  ·
                    refine ⟨69904615479242785492309397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46603076986161856994872931 69904615479242785492309397)
                    ·
                      refine ⟨3276778850589505569952003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69904615479242785492309397 3276778850589505569952003)
                      ·
                        rfl

theorem cell23_6381504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_6381504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381504 prefixEnd_6381504 := by exact prefixLift 6381504
  have htrace : WordTrace (prefixWord ++ tailWord_6381504) baseStart_6381504 baseEnd_6381504 := by
    simpa [prefixWord, tailWord_6381504, baseEnd_6381504] using wordTrace_append hprefix tailTrace_6381504
  have hstable : (prefixWord ++ tailWord_6381504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381504).length < 2 ^ (prefixWord ++ tailWord_6381504).sum := by decide
  have hdescent : baseEnd_6381504 < baseStart_6381504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381514 : List Nat := [3, 1, 2, 1, 2, 1, 4, 9]
def baseStart_6381514 : Nat := 118140960795 + 6381514 * 2 ^ 59
def prefixEnd_6381514 : Nat := 4983230072969 + 3 ^ 40 * 6381514 * 2
def baseEnd_6381514 : Nat := 121362369829483352993591

theorem tailTrace_6381514 : CollatzResearch.WordTrace tailWord_6381514 prefixEnd_6381514 121362369829483352993591 := by
  unfold tailWord_6381514
  simp only [CollatzResearch.WordTrace]
  refine ⟨58188234250718032166715899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155168624668581419111242397 58188234250718032166715899)
  ·
    refine ⟨87282351376077048250073849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58188234250718032166715899 87282351376077048250073849)
    ·
      refine ⟨65461763532057786187555387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87282351376077048250073849 65461763532057786187555387)
      ·
        refine ⟨98192645298086679281333081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65461763532057786187555387 98192645298086679281333081)
        ·
          refine ⟨73644483973565009460999811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98192645298086679281333081 73644483973565009460999811)
          ·
            refine ⟨110466725960347514191499717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73644483973565009460999811 110466725960347514191499717)
            ·
              refine ⟨20712511117565158910906197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110466725960347514191499717 20712511117565158910906197)
              ·
                refine ⟨121362369829483352993591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20712511117565158910906197 121362369829483352993591)
                ·
                  rfl

theorem cell23_6381514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 9].length) (baseStart_6381514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381514 prefixEnd_6381514 := by exact prefixLift 6381514
  have htrace : WordTrace (prefixWord ++ tailWord_6381514) baseStart_6381514 baseEnd_6381514 := by
    simpa [prefixWord, tailWord_6381514, baseEnd_6381514] using wordTrace_append hprefix tailTrace_6381514
  have hstable : (prefixWord ++ tailWord_6381514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381514).length < 2 ^ (prefixWord ++ tailWord_6381514).sum := by decide
  have hdescent : baseEnd_6381514 < baseStart_6381514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381525 : List Nat := [1, 3, 2, 3, 2, 2, 3, 1, 1, 1, 4]
def baseStart_6381525 : Nat := 118140960795 + 6381525 * 2 ^ 59
def prefixEnd_6381525 : Nat := 4983230072969 + 3 ^ 40 * 6381525 * 2
def baseEnd_6381525 : Nat := 3276789633683249987789407

theorem tailTrace_6381525 : CollatzResearch.WordTrace tailWord_6381525 prefixEnd_6381525 3276789633683249987789407 := by
  unfold tailWord_6381525
  simp only [CollatzResearch.WordTrace]
  refine ⟨232753338205832277545514029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155168892137221518363676019 232753338205832277545514029)
  ·
    refine ⟨87282501827187104079567761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232753338205832277545514029 87282501827187104079567761)
    ·
      refine ⟨65461876370390328059675821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87282501827187104079567761 65461876370390328059675821)
      ·
        refine ⟨24548203638896373022378433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65461876370390328059675821 24548203638896373022378433)
        ·
          refine ⟨18411152729172279766783825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24548203638896373022378433 18411152729172279766783825)
          ·
            refine ⟨13808364546879209825087869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18411152729172279766783825 13808364546879209825087869)
            ·
              refine ⟨5178136705079703684407951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13808364546879209825087869 5178136705079703684407951)
              ·
                refine ⟨7767205057619555526611927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5178136705079703684407951 7767205057619555526611927)
                ·
                  refine ⟨11650807586429333289917891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7767205057619555526611927 11650807586429333289917891)
                  ·
                    refine ⟨17476211379643999934876837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11650807586429333289917891 17476211379643999934876837)
                    ·
                      refine ⟨3276789633683249987789407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17476211379643999934876837 3276789633683249987789407)
                      ·
                        rfl

theorem cell23_6381525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_6381525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381525 prefixEnd_6381525 := by exact prefixLift 6381525
  have htrace : WordTrace (prefixWord ++ tailWord_6381525) baseStart_6381525 baseEnd_6381525 := by
    simpa [prefixWord, tailWord_6381525, baseEnd_6381525] using wordTrace_append hprefix tailTrace_6381525
  have hstable : (prefixWord ++ tailWord_6381525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381525).length < 2 ^ (prefixWord ++ tailWord_6381525).sum := by decide
  have hdescent : baseEnd_6381525 < baseStart_6381525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381621 : List Nat := [1, 3, 3, 1, 1, 1, 4, 2, 7]
def baseStart_6381621 : Nat := 118140960795 + 6381621 * 2 ^ 59
def prefixEnd_6381621 : Nat := 4983230072969 + 3 ^ 40 * 6381621 * 2
def baseEnd_6381621 : Nat := 364093214202897956909885

theorem tailTrace_6381621 : CollatzResearch.WordTrace tailWord_6381621 prefixEnd_6381621 364093214202897956909885 := by
  unfold tailWord_6381621
  simp only [CollatzResearch.WordTrace]
  refine ⟨232756839613484485941008717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155171226408989657294005811 232756839613484485941008717)
  ·
    refine ⟨87283814855056682227878269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232756839613484485941008717 87283814855056682227878269)
    ·
      refine ⟨32731430570646255835454351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87283814855056682227878269 32731430570646255835454351)
      ·
        refine ⟨49097145855969383753181527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32731430570646255835454351 49097145855969383753181527)
        ·
          refine ⟨73645718783954075629772291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49097145855969383753181527 73645718783954075629772291)
          ·
            refine ⟨110468578175931113444658437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73645718783954075629772291 110468578175931113444658437)
            ·
              refine ⟨20712858407987083770873457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110468578175931113444658437 20712858407987083770873457)
              ·
                refine ⟨15534643805990312828155093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20712858407987083770873457 15534643805990312828155093)
                ·
                  refine ⟨364093214202897956909885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15534643805990312828155093 364093214202897956909885)
                  ·
                    rfl

theorem cell23_6381621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 7].length) (baseStart_6381621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381621 prefixEnd_6381621 := by exact prefixLift 6381621
  have htrace : WordTrace (prefixWord ++ tailWord_6381621) baseStart_6381621 baseEnd_6381621 := by
    simpa [prefixWord, tailWord_6381621, baseEnd_6381621] using wordTrace_append hprefix tailTrace_6381621
  have hstable : (prefixWord ++ tailWord_6381621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381621).length < 2 ^ (prefixWord ++ tailWord_6381621).sum := by decide
  have hdescent : baseEnd_6381621 < baseStart_6381621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381631 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 3]
def baseStart_6381631 : Nat := 118140960795 + 6381631 * 2 ^ 59
def prefixEnd_6381631 : Nat := 4983230072969 + 3 ^ 40 * 6381631 * 2
def baseEnd_6381631 : Nat := 3276844062632626573063919

theorem tailTrace_6381631 : CollatzResearch.WordTrace tailWord_6381631 prefixEnd_6381631 3276844062632626573063919 := by
  unfold tailWord_6381631
  simp only [CollatzResearch.WordTrace]
  refine ⟨232757204343448257648872747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155171469562298838432581831 232757204343448257648872747)
  ·
    refine ⟨349135806515172386473309121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232757204343448257648872747 349135806515172386473309121)
    ·
      refine ⟨261851854886379289854981841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349135806515172386473309121 261851854886379289854981841)
      ·
        refine ⟨196388891164784467391236381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261851854886379289854981841 196388891164784467391236381)
        ·
          refine ⟨73645834186794175271713643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196388891164784467391236381 73645834186794175271713643)
          ·
            refine ⟨110468751280191262907570465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73645834186794175271713643 110468751280191262907570465)
            ·
              refine ⟨82851563460143447180677849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110468751280191262907570465 82851563460143447180677849)
              ·
                refine ⟨62138672595107585385508387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82851563460143447180677849 62138672595107585385508387)
                ·
                  refine ⟨93208008892661378078262581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62138672595107585385508387 93208008892661378078262581)
                  ·
                    refine ⟨8738250833687004194837117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93208008892661378078262581 8738250833687004194837117)
                    ·
                      refine ⟨3276844062632626573063919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8738250833687004194837117 3276844062632626573063919)
                      ·
                        rfl

theorem cell23_6381631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_6381631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381631 prefixEnd_6381631 := by exact prefixLift 6381631
  have htrace : WordTrace (prefixWord ++ tailWord_6381631) baseStart_6381631 baseEnd_6381631 := by
    simpa [prefixWord, tailWord_6381631, baseEnd_6381631] using wordTrace_append hprefix tailTrace_6381631
  have hstable : (prefixWord ++ tailWord_6381631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381631).length < 2 ^ (prefixWord ++ tailWord_6381631).sum := by decide
  have hdescent : baseEnd_6381631 < baseStart_6381631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381658 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2]
def baseStart_6381658 : Nat := 118140960795 + 6381658 * 2 ^ 59
def prefixEnd_6381658 : Nat := 4983230072969 + 3 ^ 40 * 6381658 * 2
def baseEnd_6381658 : Nat := 3276857926610297967426295

theorem tailTrace_6381658 : CollatzResearch.WordTrace tailWord_6381658 prefixEnd_6381658 3276857926610297967426295 := by
  unfold tailWord_6381658
  simp only [CollatzResearch.WordTrace]
  refine ⟨58189547278587610315026407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155172126076233627506737085 58189547278587610315026407)
  ·
    refine ⟨87284320917881415472539611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58189547278587610315026407 87284320917881415472539611)
    ·
      refine ⟨130926481376822123208809417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87284320917881415472539611 130926481376822123208809417)
      ·
        refine ⟨98194861032616592406607063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130926481376822123208809417 98194861032616592406607063)
        ·
          refine ⟨147292291548924888609910595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98194861032616592406607063 147292291548924888609910595)
          ·
            refine ⟨220938437323387332914865893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147292291548924888609910595 220938437323387332914865893)
            ·
              refine ⟨41425956998135124921537355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 220938437323387332914865893 41425956998135124921537355)
              ·
                refine ⟨62138935497202687382306033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41425956998135124921537355 62138935497202687382306033)
                ·
                  refine ⟨46604201622902015536729525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62138935497202687382306033 46604201622902015536729525)
                  ·
                    refine ⟨4369143902147063956568393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46604201622902015536729525 4369143902147063956568393)
                    ·
                      refine ⟨3276857926610297967426295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4369143902147063956568393 3276857926610297967426295)
                      ·
                        rfl

theorem cell23_6381658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_6381658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381658 prefixEnd_6381658 := by exact prefixLift 6381658
  have htrace : WordTrace (prefixWord ++ tailWord_6381658) baseStart_6381658 baseEnd_6381658 := by
    simpa [prefixWord, tailWord_6381658, baseEnd_6381658] using wordTrace_append hprefix tailTrace_6381658
  have hstable : (prefixWord ++ tailWord_6381658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381658).length < 2 ^ (prefixWord ++ tailWord_6381658).sum := by decide
  have hdescent : baseEnd_6381658 < baseStart_6381658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381688 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 4, 4, 2]
def baseStart_6381688 : Nat := 118140960795 + 6381688 * 2 ^ 59
def prefixEnd_6381688 : Nat := 4983230072969 + 3 ^ 40 * 6381688 * 2
def baseEnd_6381688 : Nat := 3276873331029932850051157

theorem tailTrace_6381688 : CollatzResearch.WordTrace tailWord_6381688 prefixEnd_6381688 3276873331029932850051157 := by
  unfold tailWord_6381688
  simp only [CollatzResearch.WordTrace]
  refine ⟨116379641652120878191848859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155172855536161170922465145 116379641652120878191848859)
  ·
    refine ⟨174569462478181317287773289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116379641652120878191848859 174569462478181317287773289)
    ·
      refine ⟨130927096858635987965829967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174569462478181317287773289 130927096858635987965829967)
      ·
        refine ⟨196390645287953981948744951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130927096858635987965829967 196390645287953981948744951)
        ·
          refine ⟨294585967931930972923117427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196390645287953981948744951 294585967931930972923117427)
          ·
            refine ⟨441878951897896459384676141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294585967931930972923117427 441878951897896459384676141)
            ·
              refine ⟨165704606961711172269253553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 441878951897896459384676141 165704606961711172269253553)
              ·
                refine ⟨124278455221283379201940165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165704606961711172269253553 124278455221283379201940165)
                ·
                  refine ⟨23302210353990633600363781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124278455221283379201940165 23302210353990633600363781)
                  ·
                    refine ⟨4369164441373243800068209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23302210353990633600363781 4369164441373243800068209)
                    ·
                      refine ⟨3276873331029932850051157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4369164441373243800068209 3276873331029932850051157)
                      ·
                        rfl

theorem cell23_6381688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 4, 4, 2].length) (baseStart_6381688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381688 prefixEnd_6381688 := by exact prefixLift 6381688
  have htrace : WordTrace (prefixWord ++ tailWord_6381688) baseStart_6381688 baseEnd_6381688 := by
    simpa [prefixWord, tailWord_6381688, baseEnd_6381688] using wordTrace_append hprefix tailTrace_6381688
  have hstable : (prefixWord ++ tailWord_6381688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381688).length < 2 ^ (prefixWord ++ tailWord_6381688).sum := by decide
  have hdescent : baseEnd_6381688 < baseStart_6381688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381722 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2]
def baseStart_6381722 : Nat := 118140960795 + 6381722 * 2 ^ 59
def prefixEnd_6381722 : Nat := 4983230072969 + 3 ^ 40 * 6381722 * 2
def baseEnd_6381722 : Nat := 3276890789372185717026001

theorem tailTrace_6381722 : CollatzResearch.WordTrace tailWord_6381722 prefixEnd_6381722 3276890789372185717026001 := by
  unfold tailWord_6381722
  simp only [CollatzResearch.WordTrace]
  refine ⟨58190130846529645047608855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155173682257412386793623613 58190130846529645047608855)
  ·
    refine ⟨87285196269794467571413283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58190130846529645047608855 87285196269794467571413283)
    ·
      refine ⟨130927794404691701357119925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87285196269794467571413283 130927794404691701357119925)
      ·
        refine ⟨12274480725439847002229993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130927794404691701357119925 12274480725439847002229993)
        ·
          refine ⟨9205860544079885251672495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12274480725439847002229993 9205860544079885251672495)
          ·
            refine ⟨13808790816119827877508743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9205860544079885251672495 13808790816119827877508743)
            ·
              refine ⟨20713186224179741816263115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13808790816119827877508743 20713186224179741816263115)
              ·
                refine ⟨31069779336269612724394673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20713186224179741816263115 31069779336269612724394673)
                ·
                  refine ⟨23302334502202209543296005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31069779336269612724394673 23302334502202209543296005)
                  ·
                    refine ⟨4369187719162914289368001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23302334502202209543296005 4369187719162914289368001)
                    ·
                      refine ⟨3276890789372185717026001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4369187719162914289368001 3276890789372185717026001)
                      ·
                        rfl

theorem cell23_6381722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_6381722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381722 prefixEnd_6381722 := by exact prefixLift 6381722
  have htrace : WordTrace (prefixWord ++ tailWord_6381722) baseStart_6381722 baseEnd_6381722 := by
    simpa [prefixWord, tailWord_6381722, baseEnd_6381722] using wordTrace_append hprefix tailTrace_6381722
  have hstable : (prefixWord ++ tailWord_6381722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381722).length < 2 ^ (prefixWord ++ tailWord_6381722).sum := by decide
  have hdescent : baseEnd_6381722 < baseStart_6381722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381728 : List Nat := [2, 1, 1, 4, 2, 2, 2, 3, 6]
def baseStart_6381728 : Nat := 118140960795 + 6381728 * 2 ^ 59
def prefixEnd_6381728 : Nat := 4983230072969 + 3 ^ 40 * 6381728 * 2
def baseEnd_6381728 : Nat := 364099318917345854838997

theorem tailTrace_6381728 : CollatzResearch.WordTrace tailWord_6381728 prefixEnd_6381728 364099318917345854838997 := by
  unfold tailWord_6381728
  simp only [CollatzResearch.WordTrace]
  refine ⟨116380371112048421607576919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155173828149397895476769225 116380371112048421607576919)
  ·
    refine ⟨174570556668072632411365379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116380371112048421607576919 174570556668072632411365379)
    ·
      refine ⟨261855835002108948617048069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174570556668072632411365379 261855835002108948617048069)
      ·
        refine ⟨49097969062895427865696513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261855835002108948617048069 49097969062895427865696513)
        ·
          refine ⟨36823476797171570899272385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49097969062895427865696513 36823476797171570899272385)
          ·
            refine ⟨27617607597878678174454289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36823476797171570899272385 27617607597878678174454289)
            ·
              refine ⟨20713205698409008630840717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27617607597878678174454289 20713205698409008630840717)
              ·
                refine ⟨7767452136903378236565269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20713205698409008630840717 7767452136903378236565269)
                ·
                  refine ⟨364099318917345854838997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7767452136903378236565269 364099318917345854838997)
                  ·
                    rfl

theorem cell23_6381728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 6].length) (baseStart_6381728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381728 prefixEnd_6381728 := by exact prefixLift 6381728
  have htrace : WordTrace (prefixWord ++ tailWord_6381728) baseStart_6381728 baseEnd_6381728 := by
    simpa [prefixWord, tailWord_6381728, baseEnd_6381728] using wordTrace_append hprefix tailTrace_6381728
  have hstable : (prefixWord ++ tailWord_6381728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381728).length < 2 ^ (prefixWord ++ tailWord_6381728).sum := by decide
  have hdescent : baseEnd_6381728 < baseStart_6381728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381762 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 8]
def baseStart_6381762 : Nat := 118140960795 + 6381762 * 2 ^ 59
def prefixEnd_6381762 : Nat := 4983230072969 + 3 ^ 40 * 6381762 * 2
def baseEnd_6381762 : Nat := 364101258733151728947313

theorem tailTrace_6381762 : CollatzResearch.WordTrace tailWord_6381762 prefixEnd_6381762 364101258733151728947313 := by
  unfold tailWord_6381762
  simp only [CollatzResearch.WordTrace]
  refine ⟨58190495576493416755472885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155174654870649111347927693 58190495576493416755472885)
  ·
    refine ⟨5455358960296257820825583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58190495576493416755472885 5455358960296257820825583)
    ·
      refine ⟨8183038440444386731238375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5455358960296257820825583 8183038440444386731238375)
      ·
        refine ⟨12274557660666580096857563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8183038440444386731238375 12274557660666580096857563)
        ·
          refine ⟨18411836490999870145286345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12274557660666580096857563 18411836490999870145286345)
          ·
            refine ⟨13808877368249902608964759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18411836490999870145286345 13808877368249902608964759)
            ·
              refine ⟨20713316052374853913447139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13808877368249902608964759 20713316052374853913447139)
              ·
                refine ⟨31069974078562280870170709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20713316052374853913447139 31069974078562280870170709)
                ·
                  refine ⟨364101258733151728947313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31069974078562280870170709 364101258733151728947313)
                  ·
                    rfl

theorem cell23_6381762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_6381762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381762 prefixEnd_6381762 := by exact prefixLift 6381762
  have htrace : WordTrace (prefixWord ++ tailWord_6381762) baseStart_6381762 baseEnd_6381762 := by
    simpa [prefixWord, tailWord_6381762, baseEnd_6381762] using wordTrace_append hprefix tailTrace_6381762
  have hstable : (prefixWord ++ tailWord_6381762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381762).length < 2 ^ (prefixWord ++ tailWord_6381762).sum := by decide
  have hdescent : baseEnd_6381762 < baseStart_6381762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381765 : List Nat := [1, 3, 1, 1, 1, 1, 4, 4, 2, 3, 2]
def baseStart_6381765 : Nat := 118140960795 + 6381765 * 2 ^ 59
def prefixEnd_6381765 : Nat := 4983230072969 + 3 ^ 40 * 6381765 * 2
def baseEnd_6381765 : Nat := 3276912869040329048788303

theorem tailTrace_6381765 : CollatzResearch.WordTrace tailWord_6381765 prefixEnd_6381765 3276912869040329048788303 := by
  unfold tailWord_6381765
  simp only [CollatzResearch.WordTrace]
  refine ⟨232762091724962798534250749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155174727816641865689500499 232762091724962798534250749)
  ·
    refine ⟨87285784396861049450344031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232762091724962798534250749 87285784396861049450344031)
    ·
      refine ⟨130928676595291574175516047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87285784396861049450344031 130928676595291574175516047)
      ·
        refine ⟨196393014892937361263274071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130928676595291574175516047 196393014892937361263274071)
        ·
          refine ⟨294589522339406041894911107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196393014892937361263274071 294589522339406041894911107)
          ·
            refine ⟨441884283509109062842366661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294589522339406041894911107 441884283509109062842366661)
            ·
              refine ⟨82853303157957949282943749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 441884283509109062842366661 82853303157957949282943749)
              ·
                refine ⟨15534994342117115490551953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82853303157957949282943749 15534994342117115490551953)
                ·
                  refine ⟨11651245756587836617913965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15534994342117115490551953 11651245756587836617913965)
                  ·
                    refine ⟨4369217158720438731717737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11651245756587836617913965 4369217158720438731717737)
                    ·
                      refine ⟨3276912869040329048788303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4369217158720438731717737 3276912869040329048788303)
                      ·
                        rfl

theorem cell23_6381765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 3, 2].length) (baseStart_6381765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381765 prefixEnd_6381765 := by exact prefixLift 6381765
  have htrace : WordTrace (prefixWord ++ tailWord_6381765) baseStart_6381765 baseEnd_6381765 := by
    simpa [prefixWord, tailWord_6381765, baseEnd_6381765] using wordTrace_append hprefix tailTrace_6381765
  have hstable : (prefixWord ++ tailWord_6381765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381765).length < 2 ^ (prefixWord ++ tailWord_6381765).sum := by decide
  have hdescent : baseEnd_6381765 < baseStart_6381765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381801 : List Nat := [1, 2, 1, 1, 1, 2, 2, 13]
def baseStart_6381801 : Nat := 118140960795 + 6381801 * 2 ^ 59
def prefixEnd_6381801 : Nat := 4983230072969 + 3 ^ 40 * 6381801 * 2
def baseEnd_6381801 : Nat := 121367827938662626219931

theorem tailTrace_6381801 : CollatzResearch.WordTrace tailWord_6381801 prefixEnd_6381801 121367827938662626219931 := by
  unfold tailWord_6381801
  simp only [CollatzResearch.WordTrace]
  refine ⟨232763404752832376682561257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155175603168554917788374171 232763404752832376682561257)
  ·
    refine ⟨174572553564624282511920943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232763404752832376682561257 174572553564624282511920943)
    ·
      refine ⟨261858830346936423767881415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174572553564624282511920943 261858830346936423767881415)
      ·
        refine ⟨392788245520404635651822123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261858830346936423767881415 392788245520404635651822123)
        ·
          refine ⟨589182368280606953477733185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392788245520404635651822123 589182368280606953477733185)
          ·
            refine ⟨441886776210455215108299889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 589182368280606953477733185 441886776210455215108299889)
            ·
              refine ⟨331415082157841411331224917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441886776210455215108299889 331415082157841411331224917)
              ·
                refine ⟨121367827938662626219931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 331415082157841411331224917 121367827938662626219931)
                ·
                  rfl

theorem cell23_6381801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 13].length) (baseStart_6381801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381801 prefixEnd_6381801 := by exact prefixLift 6381801
  have htrace : WordTrace (prefixWord ++ tailWord_6381801) baseStart_6381801 baseEnd_6381801 := by
    simpa [prefixWord, tailWord_6381801, baseEnd_6381801] using wordTrace_append hprefix tailTrace_6381801
  have hstable : (prefixWord ++ tailWord_6381801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381801).length < 2 ^ (prefixWord ++ tailWord_6381801).sum := by decide
  have hdescent : baseEnd_6381801 < baseStart_6381801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381808 : List Nat := [2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 4]
def baseStart_6381808 : Nat := 118140960795 + 6381808 * 2 ^ 59
def prefixEnd_6381808 : Nat := 4983230072969 + 3 ^ 40 * 6381808 * 2
def baseEnd_6381808 : Nat := 3276934948708472380550605

theorem tailTrace_6381808 : CollatzResearch.WordTrace tailWord_6381808 prefixEnd_6381808 3276934948708472380550605 := by
  unfold tailWord_6381808
  simp only [CollatzResearch.WordTrace]
  refine ⟨116381830031903508439033039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155175773375871344585377385 116381830031903508439033039)
  ·
    refine ⟨174572745047855262658549559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116381830031903508439033039 174572745047855262658549559)
    ·
      refine ⟨261859117571782893987824339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174572745047855262658549559 261859117571782893987824339)
      ·
        refine ⟨392788676357674340981736509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261859117571782893987824339 392788676357674340981736509)
        ·
          refine ⟨147295753634127877868151191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392788676357674340981736509 147295753634127877868151191)
          ·
            refine ⟨220943630451191816802226787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147295753634127877868151191 220943630451191816802226787)
            ·
              refine ⟨331415445676787725203340181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220943630451191816802226787 331415445676787725203340181)
              ·
                refine ⟨15535099016099424618906571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 331415445676787725203340181 15535099016099424618906571)
                ·
                  refine ⟨23302648524149136928359857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15535099016099424618906571 23302648524149136928359857)
                  ·
                    refine ⟨17476986393111852696269893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23302648524149136928359857 17476986393111852696269893)
                    ·
                      refine ⟨3276934948708472380550605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17476986393111852696269893 3276934948708472380550605)
                      ·
                        rfl

theorem cell23_6381808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 4].length) (baseStart_6381808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381808 prefixEnd_6381808 := by exact prefixLift 6381808
  have htrace : WordTrace (prefixWord ++ tailWord_6381808) baseStart_6381808 baseEnd_6381808 := by
    simpa [prefixWord, tailWord_6381808, baseEnd_6381808] using wordTrace_append hprefix tailTrace_6381808
  have hstable : (prefixWord ++ tailWord_6381808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381808).length < 2 ^ (prefixWord ++ tailWord_6381808).sum := by decide
  have hdescent : baseEnd_6381808 < baseStart_6381808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381818 : List Nat := [3, 1, 1, 1, 1, 7, 9]
def baseStart_6381818 : Nat := 118140960795 + 6381818 * 2 ^ 59
def prefixEnd_6381818 : Nat := 4983230072969 + 3 ^ 40 * 6381818 * 2
def baseEnd_6381818 : Nat := 40456050413765646190439

theorem tailTrace_6381818 : CollatzResearch.WordTrace tailWord_6381818 prefixEnd_6381818 40456050413765646190439 := by
  unfold tailWord_6381818
  simp only [CollatzResearch.WordTrace]
  refine ⟨58191006198442697146482527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155176016529180525723953405 58191006198442697146482527)
  ·
    refine ⟨87286509297664045719723791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58191006198442697146482527 87286509297664045719723791)
    ·
      refine ⟨130929763946496068579585687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87286509297664045719723791 130929763946496068579585687)
      ·
        refine ⟨196394645919744102869378531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130929763946496068579585687 196394645919744102869378531)
        ·
          refine ⟨294591968879616154304067797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196394645919744102869378531 294591968879616154304067797)
          ·
            refine ⟨6904499270616003616501589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 294591968879616154304067797 6904499270616003616501589)
            ·
              refine ⟨40456050413765646190439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6904499270616003616501589 40456050413765646190439)
              ·
                rfl

theorem cell23_6381818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 9].length) (baseStart_6381818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381818 prefixEnd_6381818 := by exact prefixLift 6381818
  have htrace : WordTrace (prefixWord ++ tailWord_6381818) baseStart_6381818 baseEnd_6381818 := by
    simpa [prefixWord, tailWord_6381818, baseEnd_6381818] using wordTrace_append hprefix tailTrace_6381818
  have hstable : (prefixWord ++ tailWord_6381818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381818).length < 2 ^ (prefixWord ++ tailWord_6381818).sum := by decide
  have hdescent : baseEnd_6381818 < baseStart_6381818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381822 : List Nat := [4, 2, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_6381822 : Nat := 118140960795 + 6381822 * 2 ^ 59
def prefixEnd_6381822 : Nat := 4983230072969 + 3 ^ 40 * 6381822 * 2
def baseEnd_6381822 : Nat := 1092314045812545108591847

theorem tailTrace_6381822 : CollatzResearch.WordTrace tailWord_6381822 prefixEnd_6381822 1092314045812545108591847 := by
  unfold tailWord_6381822
  simp only [CollatzResearch.WordTrace]
  refine ⟨29095521335719537158634465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155176113790504198179383813 29095521335719537158634465)
  ·
    refine ⟨21821641001789652868975849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29095521335719537158634465 21821641001789652868975849)
    ·
      refine ⟨16366230751342239651731887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21821641001789652868975849 16366230751342239651731887)
      ·
        refine ⟨24549346127013359477597831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16366230751342239651731887 24549346127013359477597831)
        ·
          refine ⟨36824019190520039216396747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24549346127013359477597831 36824019190520039216396747)
          ·
            refine ⟨55236028785780058824595121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36824019190520039216396747 55236028785780058824595121)
            ·
              refine ⟨41427021589335044118446341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55236028785780058824595121 41427021589335044118446341)
              ·
                refine ⟨7767566548000320772208689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41427021589335044118446341 7767566548000320772208689)
                ·
                  refine ⟨5825674911000240579156517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7767566548000320772208689 5825674911000240579156517)
                  ·
                    refine ⟨1092314045812545108591847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5825674911000240579156517 1092314045812545108591847)
                    ·
                      rfl

theorem cell23_6381822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_6381822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381822 prefixEnd_6381822 := by exact prefixLift 6381822
  have htrace : WordTrace (prefixWord ++ tailWord_6381822) baseStart_6381822 baseEnd_6381822 := by
    simpa [prefixWord, tailWord_6381822, baseEnd_6381822] using wordTrace_append hprefix tailTrace_6381822
  have hstable : (prefixWord ++ tailWord_6381822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381822).length < 2 ^ (prefixWord ++ tailWord_6381822).sum := by decide
  have hdescent : baseEnd_6381822 < baseStart_6381822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381838 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_6381838 : Nat := 118140960795 + 6381838 * 2 ^ 59
def prefixEnd_6381838 : Nat := 4983230072969 + 3 ^ 40 * 6381838 * 2
def baseEnd_6381838 : Nat := 3276950353128107263175467

theorem tailTrace_6381838 : CollatzResearch.WordTrace tailWord_6381838 prefixEnd_6381838 3276950353128107263175467 := by
  unfold tailWord_6381838
  simp only [CollatzResearch.WordTrace]
  refine ⟨29095594281712291500207271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155176502835798888001105445 29095594281712291500207271)
  ·
    refine ⟨43643391422568437250310907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29095594281712291500207271 43643391422568437250310907)
    ·
      refine ⟨65465087133852655875466361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43643391422568437250310907 65465087133852655875466361)
      ·
        refine ⟨49098815350389491906599771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65465087133852655875466361 49098815350389491906599771)
        ·
          refine ⟨73648223025584237859899657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49098815350389491906599771 73648223025584237859899657)
          ·
            refine ⟨55236167269188178394924743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73648223025584237859899657 55236167269188178394924743)
            ·
              refine ⟨82854250903782267592387115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55236167269188178394924743 82854250903782267592387115)
              ·
                refine ⟨124281376355673401388580673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82854250903782267592387115 124281376355673401388580673)
                ·
                  refine ⟨93211032266755051041435505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124281376355673401388580673 93211032266755051041435505)
                  ·
                    refine ⟨69908274200066288281076629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93211032266755051041435505 69908274200066288281076629)
                    ·
                      refine ⟨3276950353128107263175467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69908274200066288281076629 3276950353128107263175467)
                      ·
                        rfl

theorem cell23_6381838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_6381838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381838 prefixEnd_6381838 := by exact prefixLift 6381838
  have htrace : WordTrace (prefixWord ++ tailWord_6381838) baseStart_6381838 baseEnd_6381838 := by
    simpa [prefixWord, tailWord_6381838, baseEnd_6381838] using wordTrace_append hprefix tailTrace_6381838
  have hstable : (prefixWord ++ tailWord_6381838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381838).length < 2 ^ (prefixWord ++ tailWord_6381838).sum := by decide
  have hdescent : baseEnd_6381838 < baseStart_6381838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381863 : List Nat := [1, 1, 8, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_6381863 : Nat := 118140960795 + 6381863 * 2 ^ 59
def prefixEnd_6381863 : Nat := 4983230072969 + 3 ^ 40 * 6381863 * 2
def baseEnd_6381863 : Nat := 3276963190144469665362853

theorem tailTrace_6381863 : CollatzResearch.WordTrace tailWord_6381863 prefixEnd_6381863 3276963190144469665362853 := by
  unfold tailWord_6381863
  simp only [CollatzResearch.WordTrace]
  refine ⟨232765666078607761271318243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155177110719071840847545495 232765666078607761271318243)
  ·
    refine ⟨349148499117911641906977365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232765666078607761271318243 349148499117911641906977365)
    ·
      refine ⟨4091583974038027053597391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 349148499117911641906977365 4091583974038027053597391)
      ·
        refine ⟨6137375961057040580396087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4091583974038027053597391 6137375961057040580396087)
        ·
          refine ⟨9206063941585560870594131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6137375961057040580396087 9206063941585560870594131)
          ·
            refine ⟨13809095912378341305891197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9206063941585560870594131 13809095912378341305891197)
            ·
              refine ⟨5178410967141877989709199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13809095912378341305891197 5178410967141877989709199)
              ·
                refine ⟨7767616450712816984563799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5178410967141877989709199 7767616450712816984563799)
                ·
                  refine ⟨11651424676069225476845699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7767616450712816984563799 11651424676069225476845699)
                  ·
                    refine ⟨17477137014103838215268549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11651424676069225476845699 17477137014103838215268549)
                    ·
                      refine ⟨3276963190144469665362853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17477137014103838215268549 3276963190144469665362853)
                      ·
                        rfl

theorem cell23_6381863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_6381863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381863 prefixEnd_6381863 := by exact prefixLift 6381863
  have htrace : WordTrace (prefixWord ++ tailWord_6381863) baseStart_6381863 baseEnd_6381863 := by
    simpa [prefixWord, tailWord_6381863, baseEnd_6381863] using wordTrace_append hprefix tailTrace_6381863
  have hstable : (prefixWord ++ tailWord_6381863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381863).length < 2 ^ (prefixWord ++ tailWord_6381863).sum := by decide
  have hdescent : baseEnd_6381863 < baseStart_6381863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381866 : List Nat := [3, 1, 4, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_6381866 : Nat := 118140960795 + 6381866 * 2 ^ 59
def prefixEnd_6381866 : Nat := 4983230072969 + 3 ^ 40 * 6381866 * 2
def baseEnd_6381866 : Nat := 3276964730586433153625339

theorem tailTrace_6381866 : CollatzResearch.WordTrace tailWord_6381866 prefixEnd_6381866 3276964730586433153625339 := by
  unfold tailWord_6381866
  simp only [CollatzResearch.WordTrace]
  refine ⟨58191443874399223195919363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155177183665064595189118301 58191443874399223195919363)
  ·
    refine ⟨87287165811598834793879045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58191443874399223195919363 87287165811598834793879045)
    ·
      refine ⟨16366343589674781523852321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87287165811598834793879045 16366343589674781523852321)
      ·
        refine ⟨12274757692256086142889241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16366343589674781523852321 12274757692256086142889241)
        ·
          refine ⟨9206068269192064607166931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12274757692256086142889241 9206068269192064607166931)
          ·
            refine ⟨13809102403788096910750397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9206068269192064607166931 13809102403788096910750397)
            ·
              refine ⟨5178413401420536341531399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13809102403788096910750397 5178413401420536341531399)
              ·
                refine ⟨7767620102130804512297099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5178413401420536341531399 7767620102130804512297099)
                ·
                  refine ⟨11651430153196206768445649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7767620102130804512297099 11651430153196206768445649)
                  ·
                    refine ⟨8738572614897155076334237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11651430153196206768445649 8738572614897155076334237)
                    ·
                      refine ⟨3276964730586433153625339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8738572614897155076334237 3276964730586433153625339)
                      ·
                        rfl

theorem cell23_6381866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_6381866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381866 prefixEnd_6381866 := by exact prefixLift 6381866
  have htrace : WordTrace (prefixWord ++ tailWord_6381866) baseStart_6381866 baseEnd_6381866 := by
    simpa [prefixWord, tailWord_6381866, baseEnd_6381866] using wordTrace_append hprefix tailTrace_6381866
  have hstable : (prefixWord ++ tailWord_6381866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381866).length < 2 ^ (prefixWord ++ tailWord_6381866).sum := by decide
  have hdescent : baseEnd_6381866 < baseStart_6381866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381888 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 5]
def baseStart_6381888 : Nat := 118140960795 + 6381888 * 2 ^ 59
def prefixEnd_6381888 : Nat := 4983230072969 + 3 ^ 40 * 6381888 * 2
def baseEnd_6381888 : Nat := 3276976027160832067550237

theorem tailTrace_6381888 : CollatzResearch.WordTrace tailWord_6381888 prefixEnd_6381888 3276976027160832067550237 := by
  unfold tailWord_6381888
  simp only [CollatzResearch.WordTrace]
  refine ⟨116383288951758595270489159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155177718602344793693985545 116383288951758595270489159)
  ·
    refine ⟨174574933427637892905733739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116383288951758595270489159 174574933427637892905733739)
    ·
      refine ⟨261862400141456839358600609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174574933427637892905733739 261862400141456839358600609)
      ·
        refine ⟨196396800106092629518950457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261862400141456839358600609 196396800106092629518950457)
        ·
          refine ⟨147297600079569472139212843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196396800106092629518950457 147297600079569472139212843)
          ·
            refine ⟨220946400119354208208819265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147297600079569472139212843 220946400119354208208819265)
            ·
              refine ⟨165709800089515656156614449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220946400119354208208819265 165709800089515656156614449)
              ·
                refine ⟨124282350067136742117460837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165709800089515656156614449 124282350067136742117460837)
                ·
                  refine ⟨23302940637588139147023907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124282350067136742117460837 23302940637588139147023907)
                  ·
                    refine ⟨34954410956382208720535861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23302940637588139147023907 34954410956382208720535861)
                    ·
                      refine ⟨3276976027160832067550237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34954410956382208720535861 3276976027160832067550237)
                      ·
                        rfl

theorem cell23_6381888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_6381888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381888 prefixEnd_6381888 := by exact prefixLift 6381888
  have htrace : WordTrace (prefixWord ++ tailWord_6381888) baseStart_6381888 baseEnd_6381888 := by
    simpa [prefixWord, tailWord_6381888, baseEnd_6381888] using wordTrace_append hprefix tailTrace_6381888
  have hstable : (prefixWord ++ tailWord_6381888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381888).length < 2 ^ (prefixWord ++ tailWord_6381888).sum := by decide
  have hdescent : baseEnd_6381888 < baseStart_6381888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381936 : List Nat := [2, 1, 1, 1, 4, 5, 1, 2, 2, 2, 2]
def baseStart_6381936 : Nat := 118140960795 + 6381936 * 2 ^ 59
def prefixEnd_6381936 : Nat := 4983230072969 + 3 ^ 40 * 6381936 * 2
def baseEnd_6381936 : Nat := 3277000674232247879750017

theorem tailTrace_6381936 : CollatzResearch.WordTrace tailWord_6381936 prefixEnd_6381936 3277000674232247879750017 := by
  unfold tailWord_6381936
  simp only [CollatzResearch.WordTrace]
  refine ⟨116384164303671647369362831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155178885738228863159150441 116384164303671647369362831)
  ·
    refine ⟨174576246455507471054044247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116384164303671647369362831 174576246455507471054044247)
    ·
      refine ⟨261864369683261206581066371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174576246455507471054044247 261864369683261206581066371)
      ·
        refine ⟨392796554524891809871599557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261864369683261206581066371 392796554524891809871599557)
        ·
          refine ⟨73649353973417214350924917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 392796554524891809871599557 73649353973417214350924917)
          ·
            refine ⟨6904626935007863845399211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73649353973417214350924917 6904626935007863845399211)
            ·
              refine ⟨10356940402511795768098817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6904626935007863845399211 10356940402511795768098817)
              ·
                refine ⟨7767705301883846826074113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10356940402511795768098817 7767705301883846826074113)
                ·
                  refine ⟨5825778976412885119555585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7767705301883846826074113 5825778976412885119555585)
                  ·
                    refine ⟨4369334232309663839666689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5825778976412885119555585 4369334232309663839666689)
                    ·
                      refine ⟨3277000674232247879750017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4369334232309663839666689 3277000674232247879750017)
                      ·
                        rfl

theorem cell23_6381936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 2, 2, 2].length) (baseStart_6381936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381936 prefixEnd_6381936 := by exact prefixLift 6381936
  have htrace : WordTrace (prefixWord ++ tailWord_6381936) baseStart_6381936 baseEnd_6381936 := by
    simpa [prefixWord, tailWord_6381936, baseEnd_6381936] using wordTrace_append hprefix tailTrace_6381936
  have hstable : (prefixWord ++ tailWord_6381936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381936).length < 2 ^ (prefixWord ++ tailWord_6381936).sum := by decide
  have hdescent : baseEnd_6381936 < baseStart_6381936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381953 : List Nat := [1, 2, 4, 3, 1, 2, 3, 1, 2, 2, 2]
def baseStart_6381953 : Nat := 118140960795 + 6381953 * 2 ^ 59
def prefixEnd_6381953 : Nat := 4983230072969 + 3 ^ 40 * 6381953 * 2
def baseEnd_6381953 : Nat := 3277009403403374313237439

theorem tailTrace_6381953 : CollatzResearch.WordTrace tailWord_6381953 prefixEnd_6381953 3277009403403374313237439 := by
  unfold tailWord_6381953
  simp only [CollatzResearch.WordTrace]
  refine ⟨232768948648281706642094513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155179299098854471094729675 232768948648281706642094513)
  ·
    refine ⟨174576711486211279981570885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232768948648281706642094513 174576711486211279981570885)
    ·
      refine ⟨32733133403664614996544541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174576711486211279981570885 32733133403664614996544541)
      ·
        refine ⟨12274925026374230623704203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32733133403664614996544541 12274925026374230623704203)
        ·
          refine ⟨18412387539561345935556305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12274925026374230623704203 18412387539561345935556305)
          ·
            refine ⟨13809290654671009451667229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18412387539561345935556305 13809290654671009451667229)
            ·
              refine ⟨5178483995501628544375211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13809290654671009451667229 5178483995501628544375211)
              ·
                refine ⟨7767725993252442816562817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5178483995501628544375211 7767725993252442816562817)
                ·
                  refine ⟨5825794494939332112422113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7767725993252442816562817 5825794494939332112422113)
                  ·
                    refine ⟨4369345871204499084316585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5825794494939332112422113 4369345871204499084316585)
                    ·
                      refine ⟨3277009403403374313237439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4369345871204499084316585 3277009403403374313237439)
                      ·
                        rfl

theorem cell23_6381953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_6381953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381953 prefixEnd_6381953 := by exact prefixLift 6381953
  have htrace : WordTrace (prefixWord ++ tailWord_6381953) baseStart_6381953 baseEnd_6381953 := by
    simpa [prefixWord, tailWord_6381953, baseEnd_6381953] using wordTrace_append hprefix tailTrace_6381953
  have hstable : (prefixWord ++ tailWord_6381953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381953).length < 2 ^ (prefixWord ++ tailWord_6381953).sum := by decide
  have hdescent : baseEnd_6381953 < baseStart_6381953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381975 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 4]
def baseStart_6381975 : Nat := 118140960795 + 6381975 * 2 ^ 59
def prefixEnd_6381975 : Nat := 4983230072969 + 3 ^ 40 * 6381975 * 2
def baseEnd_6381975 : Nat := 3277020699977773227162337

theorem tailTrace_6381975 : CollatzResearch.WordTrace tailWord_6381975 prefixEnd_6381975 3277020699977773227162337 := by
  unfold tailWord_6381975
  simp only [CollatzResearch.WordTrace]
  refine ⟨232769751054202004399395379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155179834036134669599596919 232769751054202004399395379)
  ·
    refine ⟨349154626581303006599093069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232769751054202004399395379 349154626581303006599093069)
    ·
      refine ⟨130932984967988627474659901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349154626581303006599093069 130932984967988627474659901)
      ·
        refine ⟨49099869362995735302997463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130932984967988627474659901 49099869362995735302997463)
        ·
          refine ⟨73649804044493602954496195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49099869362995735302997463 73649804044493602954496195)
          ·
            refine ⟨110474706066740404431744293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73649804044493602954496195 110474706066740404431744293)
            ·
              refine ⟨20714007387513825830952055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110474706066740404431744293 20714007387513825830952055)
              ·
                refine ⟨31071011081270738746428083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20714007387513825830952055 31071011081270738746428083)
                ·
                  refine ⟨46606516621906108119642125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31071011081270738746428083 46606516621906108119642125)
                  ·
                    refine ⟨17477443733214790544865797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46606516621906108119642125 17477443733214790544865797)
                    ·
                      refine ⟨3277020699977773227162337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17477443733214790544865797 3277020699977773227162337)
                      ·
                        rfl

theorem cell23_6381975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_6381975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381975 prefixEnd_6381975 := by exact prefixLift 6381975
  have htrace : WordTrace (prefixWord ++ tailWord_6381975) baseStart_6381975 baseEnd_6381975 := by
    simpa [prefixWord, tailWord_6381975, baseEnd_6381975] using wordTrace_append hprefix tailTrace_6381975
  have hstable : (prefixWord ++ tailWord_6381975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381975).length < 2 ^ (prefixWord ++ tailWord_6381975).sum := by decide
  have hdescent : baseEnd_6381975 < baseStart_6381975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382004 : List Nat := [2, 5, 2, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_6382004 : Nat := 118140960795 + 6382004 * 2 ^ 59
def prefixEnd_6382004 : Nat := 4983230072969 + 3 ^ 40 * 6382004 * 2
def baseEnd_6382004 : Nat := 3277035590916753613699705

theorem tailTrace_6382004 : CollatzResearch.WordTrace tailWord_6382004 prefixEnd_6382004 3277035590916753613699705 := by
  unfold tailWord_6382004
  simp only [CollatzResearch.WordTrace]
  refine ⟨116385404385548471176100533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155180539180731294901467377 116385404385548471176100533)
  ·
    refine ⟨10911131661145169172759425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116385404385548471176100533 10911131661145169172759425)
    ·
      refine ⟨8183348745858876879569569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10911131661145169172759425 8183348745858876879569569)
      ·
        refine ⟨6137511559394157659677177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8183348745858876879569569 6137511559394157659677177)
        ·
          refine ⟨4603133669545618244757883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6137511559394157659677177 4603133669545618244757883)
          ·
            refine ⟨6904700504318427367136825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4603133669545618244757883 6904700504318427367136825)
            ·
              refine ⟨5178525378238820525352619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6904700504318427367136825 5178525378238820525352619)
              ·
                refine ⟨7767788067358230788028929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5178525378238820525352619 7767788067358230788028929)
                ·
                  refine ⟨5825841050518673091021697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7767788067358230788028929 5825841050518673091021697)
                  ·
                    refine ⟨4369380787889004818266273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5825841050518673091021697 4369380787889004818266273)
                    ·
                      refine ⟨3277035590916753613699705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4369380787889004818266273 3277035590916753613699705)
                      ·
                        rfl

theorem cell23_6382004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_6382004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382004 prefixEnd_6382004 := by exact prefixLift 6382004
  have htrace : WordTrace (prefixWord ++ tailWord_6382004) baseStart_6382004 baseEnd_6382004 := by
    simpa [prefixWord, tailWord_6382004, baseEnd_6382004] using wordTrace_append hprefix tailTrace_6382004
  have hstable : (prefixWord ++ tailWord_6382004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382004).length < 2 ^ (prefixWord ++ tailWord_6382004).sum := by decide
  have hdescent : baseEnd_6382004 < baseStart_6382004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382025 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 2, 5, 3]
def baseStart_6382025 : Nat := 118140960795 + 6382025 * 2 ^ 59
def prefixEnd_6382025 : Nat := 4983230072969 + 3 ^ 40 * 6382025 * 2
def baseEnd_6382025 : Nat := 3277046374010498031537107

theorem tailTrace_6382025 : CollatzResearch.WordTrace tailWord_6382025 prefixEnd_6382025 3277046374010498031537107 := by
  unfold tailWord_6382025
  simp only [CollatzResearch.WordTrace]
  refine ⟨232771574704020862938715529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155181049802680575292477019 232771574704020862938715529)
  ·
    refine ⟨174578681028015647204036647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232771574704020862938715529 174578681028015647204036647)
    ·
      refine ⟨261868021542023470806054971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174578681028015647204036647 261868021542023470806054971)
      ·
        refine ⟨392802032313035206209082457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261868021542023470806054971 392802032313035206209082457)
        ·
          refine ⟨294601524234776404656811843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392802032313035206209082457 294601524234776404656811843)
          ·
            refine ⟨441902286352164606985217765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294601524234776404656811843 441902286352164606985217765)
            ·
              refine ⟨82856678691030863809728331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 441902286352164606985217765 82856678691030863809728331)
              ·
                refine ⟨124285018036546295714592497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82856678691030863809728331 124285018036546295714592497)
                ·
                  refine ⟨93213763527409721785944373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124285018036546295714592497 93213763527409721785944373)
                  ·
                    refine ⟨8738790330694661417432285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93213763527409721785944373 8738790330694661417432285)
                    ·
                      refine ⟨3277046374010498031537107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8738790330694661417432285 3277046374010498031537107)
                      ·
                        rfl

theorem cell23_6382025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 5, 3].length) (baseStart_6382025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382025 prefixEnd_6382025 := by exact prefixLift 6382025
  have htrace : WordTrace (prefixWord ++ tailWord_6382025) baseStart_6382025 baseEnd_6382025 := by
    simpa [prefixWord, tailWord_6382025, baseEnd_6382025] using wordTrace_append hprefix tailTrace_6382025
  have hstable : (prefixWord ++ tailWord_6382025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382025).length < 2 ^ (prefixWord ++ tailWord_6382025).sum := by decide
  have hdescent : baseEnd_6382025 < baseStart_6382025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382052 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 5, 5, 2]
def baseStart_6382052 : Nat := 118140960795 + 6382052 * 2 ^ 59
def prefixEnd_6382052 : Nat := 4983230072969 + 3 ^ 40 * 6382052 * 2
def baseEnd_6382052 : Nat := 3277060237988169425899483

theorem tailTrace_6382052 : CollatzResearch.WordTrace tailWord_6382052 prefixEnd_6382052 3277060237988169425899483 := by
  unfold tailWord_6382052
  simp only [CollatzResearch.WordTrace]
  refine ⟨116386279737461523274974205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155181706316615364366632273 116386279737461523274974205)
  ·
    refine ⟨43644854901548071228115327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116386279737461523274974205 43644854901548071228115327)
    ·
      refine ⟨65467282352322106842172991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43644854901548071228115327 65467282352322106842172991)
      ·
        refine ⟨98200923528483160263259487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65467282352322106842172991 98200923528483160263259487)
        ·
          refine ⟨147301385292724740394889231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98200923528483160263259487 147301385292724740394889231)
          ·
            refine ⟨220952077939087110592333847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147301385292724740394889231 220952077939087110592333847)
            ·
              refine ⟨331428116908630665888500771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220952077939087110592333847 331428116908630665888500771)
              ·
                refine ⟨497142175362945998832751157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331428116908630665888500771 497142175362945998832751157)
                ·
                  refine ⟨46607078940276187390570421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 497142175362945998832751157 46607078940276187390570421)
                  ·
                    refine ⟨4369413650650892567865977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46607078940276187390570421 4369413650650892567865977)
                    ·
                      refine ⟨3277060237988169425899483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4369413650650892567865977 3277060237988169425899483)
                      ·
                        rfl

theorem cell23_6382052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_6382052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382052 prefixEnd_6382052 := by exact prefixLift 6382052
  have htrace : WordTrace (prefixWord ++ tailWord_6382052) baseStart_6382052 baseEnd_6382052 := by
    simpa [prefixWord, tailWord_6382052, baseEnd_6382052] using wordTrace_append hprefix tailTrace_6382052
  have hstable : (prefixWord ++ tailWord_6382052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382052).length < 2 ^ (prefixWord ++ tailWord_6382052).sum := by decide
  have hdescent : baseEnd_6382052 < baseStart_6382052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382062 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 3, 5]
def baseStart_6382062 : Nat := 118140960795 + 6382062 * 2 ^ 59
def prefixEnd_6382062 : Nat := 4983230072969 + 3 ^ 40 * 6382062 * 2
def baseEnd_6382062 : Nat := 1092355124264904795591479

theorem tailTrace_6382062 : CollatzResearch.WordTrace tailWord_6382062 prefixEnd_6382062 1092355124264904795591479 := by
  unfold tailWord_6382062
  simp only [CollatzResearch.WordTrace]
  refine ⟨29096615525610852282226555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155181949469924545505208293 29096615525610852282226555)
  ·
    refine ⟨43644923288416278423339833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29096615525610852282226555 43644923288416278423339833)
    ·
      refine ⟨32733692466312208817504875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43644923288416278423339833 32733692466312208817504875)
      ·
        refine ⟨49100538699468313226257313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32733692466312208817504875 49100538699468313226257313)
        ·
          refine ⟨36825404024601234919692985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49100538699468313226257313 36825404024601234919692985)
          ·
            refine ⟨27619053018450926189769739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36825404024601234919692985 27619053018450926189769739)
            ·
              refine ⟨41428579527676389284654609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27619053018450926189769739 41428579527676389284654609)
              ·
                refine ⟨31071434645757291963490957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41428579527676389284654609 31071434645757291963490957)
                ·
                  refine ⟨11651787992158984486309109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31071434645757291963490957 11651787992158984486309109)
                  ·
                    refine ⟨1092355124264904795591479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11651787992158984486309109 1092355124264904795591479)
                    ·
                      rfl

theorem cell23_6382062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_6382062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382062 prefixEnd_6382062 := by exact prefixLift 6382062
  have htrace : WordTrace (prefixWord ++ tailWord_6382062) baseStart_6382062 baseEnd_6382062 := by
    simpa [prefixWord, tailWord_6382062, baseEnd_6382062] using wordTrace_append hprefix tailTrace_6382062
  have hstable : (prefixWord ++ tailWord_6382062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382062).length < 2 ^ (prefixWord ++ tailWord_6382062).sum := by decide
  have hdescent : baseEnd_6382062 < baseStart_6382062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382092 : List Nat := [2, 2, 1, 2, 4, 1, 2, 2, 1, 6]
def baseStart_6382092 : Nat := 118140960795 + 6382092 * 2 ^ 59
def prefixEnd_6382092 : Nat := 4983230072969 + 3 ^ 40 * 6382092 * 2
def baseEnd_6382092 : Nat := 1092360259071449756466433

theorem tailTrace_6382092 : CollatzResearch.WordTrace tailWord_6382092 prefixEnd_6382092 1092360259071449756466433 := by
  unfold tailWord_6382092
  simp only [CollatzResearch.WordTrace]
  refine ⟨116387009197389066690702265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155182678929852088920936353 116387009197389066690702265)
  ·
    refine ⟨87290256898041800018026699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116387009197389066690702265 87290256898041800018026699)
    ·
      refine ⟨130935385347062700027040049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87290256898041800018026699 130935385347062700027040049)
      ·
        refine ⟨98201539010297025020280037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130935385347062700027040049 98201539010297025020280037)
        ·
          refine ⟨18412788564430692191302507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98201539010297025020280037 18412788564430692191302507)
          ·
            refine ⟨27619182846646038286953761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18412788564430692191302507 27619182846646038286953761)
            ·
              refine ⟨20714387134984528715215321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27619182846646038286953761 20714387134984528715215321)
              ·
                refine ⟨15535790351238396536411491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20714387134984528715215321 15535790351238396536411491)
                ·
                  refine ⟨23303685526857594804617237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15535790351238396536411491 23303685526857594804617237)
                  ·
                    refine ⟨1092360259071449756466433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23303685526857594804617237 1092360259071449756466433)
                    ·
                      rfl

theorem cell23_6382092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_6382092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382092 prefixEnd_6382092 := by exact prefixLift 6382092
  have htrace : WordTrace (prefixWord ++ tailWord_6382092) baseStart_6382092 baseEnd_6382092 := by
    simpa [prefixWord, tailWord_6382092, baseEnd_6382092] using wordTrace_append hprefix tailTrace_6382092
  have hstable : (prefixWord ++ tailWord_6382092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382092).length < 2 ^ (prefixWord ++ tailWord_6382092).sum := by decide
  have hdescent : baseEnd_6382092 < baseStart_6382092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382099 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 5, 2, 2]
def baseStart_6382099 : Nat := 118140960795 + 6382099 * 2 ^ 59
def prefixEnd_6382099 : Nat := 4983230072969 + 3 ^ 40 * 6382099 * 2
def baseEnd_6382099 : Nat := 3277084371578930742011767

theorem tailTrace_6382099 : CollatzResearch.WordTrace tailWord_6382099 prefixEnd_6382099 3277084371578930742011767 := by
  unfold tailWord_6382099
  simp only [CollatzResearch.WordTrace]
  refine ⟨232774273705752773576909351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155182849137168515717939567 232774273705752773576909351)
  ·
    refine ⟨349161410558629160365364027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232774273705752773576909351 349161410558629160365364027)
    ·
      refine ⟨523742115837943740548046041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349161410558629160365364027 523742115837943740548046041)
      ·
        refine ⟨392806586878457805411034531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523742115837943740548046041 392806586878457805411034531)
        ·
          refine ⟨589209880317686708116551797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392806586878457805411034531 589209880317686708116551797)
          ·
            refine ⟨55238426279783128885926731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 589209880317686708116551797 55238426279783128885926731)
            ·
              refine ⟨82857639419674693328890097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55238426279783128885926731 82857639419674693328890097)
              ·
                refine ⟨62143229564756019996667573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82857639419674693328890097 62143229564756019996667573)
                ·
                  refine ⟨5825927771695876874687585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62143229564756019996667573 5825927771695876874687585)
                  ·
                    refine ⟨4369445828771907656015689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5825927771695876874687585 4369445828771907656015689)
                    ·
                      refine ⟨3277084371578930742011767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4369445828771907656015689 3277084371578930742011767)
                      ·
                        rfl

theorem cell23_6382099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 2, 2].length) (baseStart_6382099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382099 prefixEnd_6382099 := by exact prefixLift 6382099
  have htrace : WordTrace (prefixWord ++ tailWord_6382099) baseStart_6382099 baseEnd_6382099 := by
    simpa [prefixWord, tailWord_6382099, baseEnd_6382099] using wordTrace_append hprefix tailTrace_6382099
  have hstable : (prefixWord ++ tailWord_6382099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382099).length < 2 ^ (prefixWord ++ tailWord_6382099).sum := by decide
  have hdescent : baseEnd_6382099 < baseStart_6382099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382109 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 4, 4]
def baseStart_6382109 : Nat := 118140960795 + 6382109 * 2 ^ 59
def prefixEnd_6382109 : Nat := 4983230072969 + 3 ^ 40 * 6382109 * 2
def baseEnd_6382109 : Nat := 1092363168795158567628907

theorem tailTrace_6382109 : CollatzResearch.WordTrace tailWord_6382109 prefixEnd_6382109 1092363168795158567628907 := by
  unfold tailWord_6382109
  simp only [CollatzResearch.WordTrace]
  refine ⟨232774638435716545284773381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155183092290477696856515587 232774638435716545284773381)
  ·
    refine ⟨43645244706696852240895009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232774638435716545284773381 43645244706696852240895009)
    ·
      refine ⟨32733933530022639180671257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43645244706696852240895009 32733933530022639180671257)
      ·
        refine ⟨24550450147516979385503443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32733933530022639180671257 24550450147516979385503443)
        ·
          refine ⟨36825675221275469078255165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24550450147516979385503443 36825675221275469078255165)
          ·
            refine ⟨13809628207978300904345687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36825675221275469078255165 13809628207978300904345687)
            ·
              refine ⟨20714442311967451356518531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13809628207978300904345687 20714442311967451356518531)
              ·
                refine ⟨31071663467951177034777797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20714442311967451356518531 31071663467951177034777797)
                ·
                  refine ⟨5825936900240845694020837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31071663467951177034777797 5825936900240845694020837)
                  ·
                    refine ⟨1092363168795158567628907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5825936900240845694020837 1092363168795158567628907)
                    ·
                      rfl

theorem cell23_6382109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_6382109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382109 prefixEnd_6382109 := by exact prefixLift 6382109
  have htrace : WordTrace (prefixWord ++ tailWord_6382109) baseStart_6382109 baseEnd_6382109 := by
    simpa [prefixWord, tailWord_6382109, baseEnd_6382109] using wordTrace_append hprefix tailTrace_6382109
  have hstable : (prefixWord ++ tailWord_6382109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382109).length < 2 ^ (prefixWord ++ tailWord_6382109).sum := by decide
  have hdescent : baseEnd_6382109 < baseStart_6382109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382126 : List Nat := [4, 1, 3, 1, 3, 2, 1, 1, 1, 6]
def baseStart_6382126 : Nat := 118140960795 + 6382126 * 2 ^ 59
def prefixEnd_6382126 : Nat := 4983230072969 + 3 ^ 40 * 6382126 * 2
def baseEnd_6382126 : Nat := 1092366078518867378791381

theorem tailTrace_6382126 : CollatzResearch.WordTrace tailWord_6382126 prefixEnd_6382126 1092366078518867378791381 := by
  unfold tailWord_6382126
  simp only [CollatzResearch.WordTrace]
  refine ⟨29096907309581869648517779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155183505651103304792094821 29096907309581869648517779)
  ·
    refine ⟨43645360964372804472776669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29096907309581869648517779 43645360964372804472776669)
    ·
      refine ⟨16367010361639801677291251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43645360964372804472776669 16367010361639801677291251)
      ·
        refine ⟨24550515542459702515936877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16367010361639801677291251 24550515542459702515936877)
        ·
          refine ⟨9206443328422388443476329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24550515542459702515936877 9206443328422388443476329)
          ·
            refine ⟨6904832496316791332607247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9206443328422388443476329 6904832496316791332607247)
            ·
              refine ⟨10357248744475186998910871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6904832496316791332607247 10357248744475186998910871)
              ·
                refine ⟨15535873116712780498366307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10357248744475186998910871 15535873116712780498366307)
                ·
                  refine ⟨23303809675069170747549461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15535873116712780498366307 23303809675069170747549461)
                  ·
                    refine ⟨1092366078518867378791381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23303809675069170747549461 1092366078518867378791381)
                    ·
                      rfl

theorem cell23_6382126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_6382126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382126 prefixEnd_6382126 := by exact prefixLift 6382126
  have htrace : WordTrace (prefixWord ++ tailWord_6382126) baseStart_6382126 baseEnd_6382126 := by
    simpa [prefixWord, tailWord_6382126, baseEnd_6382126] using wordTrace_append hprefix tailTrace_6382126
  have hstable : (prefixWord ++ tailWord_6382126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382126).length < 2 ^ (prefixWord ++ tailWord_6382126).sum := by decide
  have hdescent : baseEnd_6382126 < baseStart_6382126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382149 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 4, 1, 3]
def baseStart_6382149 : Nat := 118140960795 + 6382149 * 2 ^ 59
def prefixEnd_6382149 : Nat := 4983230072969 + 3 ^ 40 * 6382149 * 2
def baseEnd_6382149 : Nat := 3277110045611655546386537

theorem tailTrace_6382149 : CollatzResearch.WordTrace tailWord_6382149 prefixEnd_6382149 3277110045611655546386537 := by
  unfold tailWord_6382149
  simp only [CollatzResearch.WordTrace]
  refine ⟨232776097355571632116229501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155184064903714421410819667 232776097355571632116229501)
  ·
    refine ⟨87291036508339362043586063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232776097355571632116229501 87291036508339362043586063)
    ·
      refine ⟨130936554762509043065379095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87291036508339362043586063 130936554762509043065379095)
      ·
        refine ⟨196404832143763564598068643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130936554762509043065379095 196404832143763564598068643)
        ·
          refine ⟨294607248215645346897102965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196404832143763564598068643 294607248215645346897102965)
          ·
            refine ⟨27619429520216751271603403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 294607248215645346897102965 27619429520216751271603403)
            ·
              refine ⟨41429144280325126907405105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27619429520216751271603403 41429144280325126907405105)
              ·
                refine ⟨31071858210243845180553829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41429144280325126907405105 31071858210243845180553829)
                ·
                  refine ⟨5825973414420720971353843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31071858210243845180553829 5825973414420720971353843)
                  ·
                    refine ⟨8738960121631081457030765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5825973414420720971353843 8738960121631081457030765)
                    ·
                      refine ⟨3277110045611655546386537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8738960121631081457030765 3277110045611655546386537)
                      ·
                        rfl

theorem cell23_6382149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 1, 3].length) (baseStart_6382149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382149 prefixEnd_6382149 := by exact prefixLift 6382149
  have htrace : WordTrace (prefixWord ++ tailWord_6382149) baseStart_6382149 baseEnd_6382149 := by
    simpa [prefixWord, tailWord_6382149, baseEnd_6382149] using wordTrace_append hprefix tailTrace_6382149
  have hstable : (prefixWord ++ tailWord_6382149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382149).length < 2 ^ (prefixWord ++ tailWord_6382149).sum := by decide
  have hdescent : baseEnd_6382149 < baseStart_6382149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
